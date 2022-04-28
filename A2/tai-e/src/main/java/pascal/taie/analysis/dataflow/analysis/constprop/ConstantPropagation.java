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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact fact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param))
                fact.update(param, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.entries().forEach(entry -> {
            Value origin = target.get(entry.getKey());
            if (origin == null) {
                target.update(entry.getKey(), entry.getValue());
            } else {
                Value newV = meetValue(origin, entry.getValue());
                target.update(entry.getKey(), newV);
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        else if (v1.isConstant() && v2.isConstant()) {
            if (v1.getConstant() == v2.getConstant())
                return Value.makeConstant(v1.getConstant());
            else
                return Value.getNAC();
        } else if (v1.isUndef()) {
            if (v2.isConstant())
                return Value.makeConstant(v2.getConstant());
            else
                return Value.getUndef();

        } else {
            if (v1.isConstant())
                return Value.makeConstant(v1.getConstant());
            else
                return Value.getUndef();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact originOut = out.copy();
        if (stmt instanceof DefinitionStmt definitionStmt) {
            LValue lexp = definitionStmt.getLValue();
            RValue rexp = definitionStmt.getRValue();
            Var newlvar = null;
            if (lexp instanceof Var) {
                newlvar = (Var) lexp;
            }
            // gen
            Value gen = evaluate(rexp, in);
            CPFact tmpFact = new CPFact();
            tmpFact.copyFrom(in);
            if (newlvar != null && canHoldInt(newlvar))
                tmpFact.update(newlvar, gen);

            return out.copyFrom(tmpFact);


//            if (lexp instanceof Var lvar) {
//                Var newlvar = null;
//                Value res = evaluate(rexp, in);
//                canHoldInt(lvar)
//                in.remove(lvar);
//                out.copyFrom(in);
//                out.update(lvar, res);
//                return !originOut.equals(out);
//            } else {
//                return out.copyFrom(in);
//            }
        } else { // if the stmt is not an assignment stmt, the node will not change
            return out.copyFrom(in);
        }
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof IntLiteral c) {
            return Value.makeConstant(c.getValue());
        } else if (exp instanceof Var v) {
            return in.get(v);
        } else if (exp instanceof BinaryExp bin) { // BinaryExp
            Value op1 = in.get(bin.getOperand1());
            Value op2 = in.get(bin.getOperand2());
            if (op1.isNAC() || op2.isNAC())
                return Value.getNAC();
            else if (op1.isConstant() && op2.isConstant()) {
                int op1_C = op1.getConstant();
                int op2_C = op2.getConstant();
                var op = bin.getOperator();
                Value value_1 = Value.makeConstant(1);
                Value value_0 = Value.makeConstant(0);

                switch (op.toString()) {
                    // arithmetic
                    case "+":
                        return Value.makeConstant(op1_C + op2_C);
                    case "-":
                        return Value.makeConstant(op1_C - op2_C);
                    case "*":
                        return Value.makeConstant(op1_C * op2_C);
                    case "/":
                        if (op2_C == 0)
                            return Value.getUndef();
                        return Value.makeConstant(op1_C / op2_C);
                    case "%":
                        if (op2_C == 0)
                            return Value.getUndef();
                        return Value.makeConstant(op1_C % op2_C);

                    case "==": // condition
                        return op1_C == op2_C ? value_1 : value_0;
                    case "!=":
                        return op1_C != op2_C ? value_1 : value_0;
                    case "<":
                        return op1_C < op2_C ? value_1 : value_0;
                    case ">":
                        return op1_C > op2_C ? value_1 : value_0;
                    case "<=":
                        return op1_C <= op2_C ? value_1 : value_0;
                    case ">=":
                        return op1_C >= op2_C ? value_1 : value_0;

                    case ">>": //shift
                        return Value.makeConstant(op1_C >> op2_C);
                    case "<<":
                        return Value.makeConstant(op1_C << op2_C);
                    case ">>>":
                        return Value.makeConstant(op1_C >>> op2_C);

                    case "|": // bit
                        return Value.makeConstant(op1_C | op2_C);
                    case "&":
                        return Value.makeConstant(op1_C & op2_C);
                    case "^":
                        return Value.makeConstant(op1_C ^ op2_C);
                    default:
                        return Value.getUndef();
                }
            } else
                return Value.getUndef();

        } else
            return Value.getNAC();

//        System.err.println("error here");
//        return null;
    }

}