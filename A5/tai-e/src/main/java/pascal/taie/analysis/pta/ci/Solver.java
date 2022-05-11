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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;


    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        // process simple statement: static field, call, new, copy
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method);
            for (Stmt stmt : method.getIR().getStmts()) {
                if (stmt instanceof Copy copy) {
                    stmtProcessor.visit(copy);
                } else if (stmt instanceof New n) {
                    stmtProcessor.visit(n);
                } else if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                    stmtProcessor.visit(loadField);
                } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                    stmtProcessor.visit(storeField);
                } else if (stmt instanceof Invoke invoke && invoke.isStatic()) {
                    stmtProcessor.visit(invoke);
                }
//                else if (stmt instanceof LoadArray loadArray) {
//                    stmtProcessor.visit(loadArray);
//                } else if (stmt instanceof StoreArray storeArray) {
//                    stmtProcessor.visit(storeArray);
//                }  e
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            // get x
            var lvar = stmt.getLValue();
            var ptrs = pointerFlowGraph.getVarPtr(lvar);

            Obj obj = heapModel.getObj(stmt);
            PointsToSet set = new PointsToSet();
            set.addObject(obj);
            // add {x,{oi}}
            workList.addEntry(ptrs, set);
            return null;
        }

        @Override
        public Void visit(LoadArray stmt) { // y <- x[i]
            var lptr = pointerFlowGraph.getVarPtr(stmt.getLValue());

            ArrayAccess arrayAccess = stmt.getArrayAccess();
            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex((Obj) arrayAccess.getBase());
            // y <- o[*]
            addPFGEdge(arrayIndex, lptr);
            return null;
        }

        @Override
        public Void visit(StoreArray stmt) {
            var rptr = pointerFlowGraph.getVarPtr(stmt.getRValue());

            ArrayAccess arrayAccess = stmt.getArrayAccess();
            var lptr = pointerFlowGraph.getVarPtr(arrayAccess.getBase());
            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex((Obj) arrayAccess.getBase());
            // o[*] <- y
            addPFGEdge(rptr, arrayIndex);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) { // y = T.f
            var lvar = stmt.getLValue();
            var varPtr = pointerFlowGraph.getVarPtr(lvar);
            var lset = varPtr.getPointsToSet();

            var field = stmt.getFieldRef().resolve();
            var pointer = pointerFlowGraph.getStaticField(field);
            var set = pointer.getPointsToSet();
//            for (Obj obj : set) {
//                lset.addObject(obj);
//            }
            // y <- T.f
            addPFGEdge(pointer, varPtr);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) { // T.f = y
            var rvar = stmt.getRValue();
            var varPtr = pointerFlowGraph.getVarPtr(rvar);
            var rset = varPtr.getPointsToSet();

            var field = stmt.getFieldRef().resolve();
            var pointer = pointerFlowGraph.getStaticField(field);
            var set = pointer.getPointsToSet();
//            for (Obj obj : set) {
//                rset.addObject(obj);
//            }
            addPFGEdge(varPtr, pointer);
            return null;
        }

        @Override
        public Void visit(Copy stmt) { // x = y
            var lvar = stmt.getLValue();
            var lVarPtr = pointerFlowGraph.getVarPtr(lvar);

            var rvar = stmt.getRValue();
            var rVarPtr = pointerFlowGraph.getVarPtr(rvar);

            // x <- y
            addPFGEdge(rVarPtr, lVarPtr);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            var lvar = stmt.getLValue();
            // for parameters
            var method = resolveCallee(null, stmt);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))) {
                addReachable(method);
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    var arg = stmt.getInvokeExp().getArg(i);
                    var argPtr = pointerFlowGraph.getVarPtr(arg);
                    var param = method.getIR().getParam(i);
                    var paramPtr = pointerFlowGraph.getVarPtr(param);
                    // ai -> mi
                    addPFGEdge(argPtr, paramPtr);

                }

                if (lvar == null)
                    return null;
                // for return vars
                var lVarPtr = pointerFlowGraph.getVarPtr(lvar);
                for (Var returnVar : method.getIR().getReturnVars()) {
                    var returnPtr = pointerFlowGraph.getVarPtr(returnVar);
                    var returnSet = returnPtr.getPointsToSet();
                    // mret -> r
                    addPFGEdge(returnPtr, lVarPtr);
                }
            }
//            stmt.getInvokeExp()
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (!pointerFlowGraph.getSuccsOf(source).contains(target)) {
            pointerFlowGraph.addEdge(source, target);
            var sset = source.getPointsToSet();
            if (!sset.isEmpty()) {
                workList.addEntry(target, sset);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet delta = propagate(ptr, entry.pointsToSet());
            if (ptr instanceof VarPtr varPtr && !delta.isEmpty()) {
                var var = varPtr.getVar();
                for (Obj obj : delta) {
                    // y = x.f
                    for (LoadField loadField : var.getLoadFields()) {
                        // y
                        var lvar = loadField.getLValue();
                        // x.f
                        var field = loadField.getFieldRef().resolve();
                        var fieldPtr = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(fieldPtr, pointerFlowGraph.getVarPtr(lvar));
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        // x.f = y
                        var rvar = storeField.getRValue();
                        // x.f
                        var field = storeField.getFieldRef().resolve();
                        var fieldPtr = pointerFlowGraph.getInstanceField(obj, field);
                        addPFGEdge(pointerFlowGraph.getVarPtr(rvar), fieldPtr);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
//                        y = x[i]
                        var lvar = loadArray.getLValue();
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayIndex, pointerFlowGraph.getVarPtr(lvar));
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
//                         x[i] = y
                        var rvar = storeArray.getRValue();
                        var arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(pointerFlowGraph.getVarPtr(rvar), arrayIndex);
                    }
                    processCall(var, obj);
                }
            }


        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var pointSet = pointer.getPointsToSet();
        PointsToSet delta = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (pointSet.addObject(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (Invoke invoke : var.getInvokes()) {
            if (invoke.isStatic())
                continue;
            var lvar = invoke.getResult();
            var callee = resolveCallee(recv, invoke);
            if (callee == null)
                continue;
            var thisVarPtr = pointerFlowGraph.getVarPtr(callee.getIR().getThis());
            PointsToSet set = new PointsToSet();
            set.addObject(recv);
            workList.addEntry(thisVarPtr, set);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, callee))) {
                addReachable(callee);
                var invokeExp = invoke.getInvokeExp();
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    var arg = invokeExp.getArg(i);
                    var param = callee.getIR().getParam(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                }
                if (lvar == null)
                    continue;
                for (Var returnVar : callee.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(lvar));
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
