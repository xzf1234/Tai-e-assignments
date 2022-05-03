/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me

        Set<Stmt> valid = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Stmt entry = cfg.getEntry();
        dfs(entry, cfg, valid, constants, liveVars);
        deadCode.addAll(ir.getStmts());
        deadCode.removeAll(valid);
        return deadCode;
//         deadCode;
    }

    void dfs(Stmt cur, CFG<Stmt> cfg,
             Set<Stmt> valid,
             DataflowResult<Stmt, CPFact> constants,
             DataflowResult<Stmt, SetFact<Var>> liveVars) {
        for (Stmt stmt : cfg.getSuccsOf(cur)) {
            if (valid.contains(stmt))
                return;
            valid.add(stmt);
            if (cfg.getInDegreeOf(stmt) == 0 && !cfg.isEntry(stmt)) {
                valid.remove(stmt);
            } else if (stmt instanceof DefinitionStmt definitionStmt) {
                var lexp = definitionStmt.getLValue();
                var rexp = definitionStmt.getRValue();
                if (lexp instanceof Var lvar && !liveVars.getOutFact(stmt).contains(lvar) && hasNoSideEffect(rexp)) {
                    valid.remove(stmt);
                }
                dfs(stmt, cfg, valid, constants, liveVars);

            } else if (stmt instanceof If ifstmt) {
                var condition = ifstmt.getCondition();
                var op = condition.getOperator();
                var lexp = condition.getOperand1();
                var lres = ConstantPropagation.evaluate(lexp, constants.getInFact(stmt));

                var rexp = condition.getOperand2();
                var rres = ConstantPropagation.evaluate(rexp, constants.getInFact(stmt));

                if (lres.isConstant() && rres.isConstant()) { //语法糖挺有意思的
                    boolean isTrue;
                    int lc = lres.getConstant();
                    int rc = rres.getConstant();
                    isTrue = switch (op) {
                        case EQ -> lc == rc;
                        case NE -> lc != rc;
                        case LT -> lc < rc;
                        case GT -> lc > rc;
                        case LE -> lc <= rc;
                        case GE -> lc >= rc;
                    };
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                        if (edge.getKind() == Edge.Kind.IF_TRUE && isTrue) {
                            // kill the true branch
                            valid.add(edge.getTarget());
                            dfs(edge.getTarget(), cfg, valid, constants, liveVars);
                        } else if (edge.getKind() == Edge.Kind.IF_FALSE && !isTrue) {
                            // kill the false branch
                            valid.add(edge.getTarget());
                            dfs(edge.getTarget(), cfg, valid, constants, liveVars);
                        }
                    }
                } else
                    dfs(stmt, cfg, valid, constants, liveVars);

            } else if (stmt instanceof SwitchStmt switchStmt) {
                var key = switchStmt.getVar();
                var keyC = ConstantPropagation.evaluate(key, constants.getInFact(stmt));
                if (keyC.isConstant()) {
                    if (switchStmt.getCaseValues().contains(keyC.getConstant())) {
                        for (Pair<Integer, Stmt> pair : switchStmt.getCaseTargets()) {
                            if (pair.first() == keyC.getConstant()) {
                                valid.add(pair.second());
                                dfs(pair.second(), cfg, valid, constants, liveVars);
                            }
                        }
                    }else { // default case
                      var defaultTarget=  switchStmt.getDefaultTarget();
                        valid.add(defaultTarget);
                        dfs(defaultTarget, cfg, valid, constants, liveVars);
                    }
                } else {
                    dfs(stmt, cfg, valid, constants, liveVars);
                }
            } else
                dfs(stmt, cfg, valid, constants, liveVars);

        }
    }


    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
