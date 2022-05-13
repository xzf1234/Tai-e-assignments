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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.concurrent.atomic.AtomicBoolean;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
        }
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
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
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        public Void visit(New stmt) {
            Context heapContext = contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt));
            var lptr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
//            Context objContext = ContextSelector.
            var csobj = csManager.getCSObj(heapContext, obj);
            PointsToSet set = PointsToSetFactory.make(csobj);
            workList.addEntry(lptr, set);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var lptr = csManager.getCSVar(context, stmt.getLValue());
            var rptr = csManager.getCSVar(context, stmt.getRValue());
            pointerFlowGraph.addEdge(rptr, lptr);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            // x = T.f
            var field = stmt.getFieldRef().resolve();
            if (!field.isStatic())
                return null;
            var lptr = csManager.getCSVar(context, stmt.getLValue());
            var fieldPtr = csManager.getStaticField(field);
            pointerFlowGraph.addEdge(fieldPtr, lptr);
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            // T.f = x
            var field = stmt.getFieldRef().resolve();
            if (!field.isStatic())
                return null;
            var rptr = csManager.getCSVar(context, stmt.getRValue());
            var fieldPtr = csManager.getStaticField(field);
            pointerFlowGraph.addEdge(rptr, fieldPtr);
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            // [x] = call(a1,a2,a3)
            if (!stmt.getInvokeExp().getMethodRef().isStatic())
                return null;
            var callee = resolveCallee(null, stmt);
            var csCallSite = csManager.getCSCallSite(context, stmt);
            Context ct = contextSelector.selectContext(csCallSite, callee);
            var csCallee = csManager.getCSMethod(ct,callee);
            if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite
                    , csManager.getCSMethod(ct, callee)))) {
                addReachable(csCallee);
                for (int i = 0; i < stmt.getInvokeExp().getArgCount(); i++) {
                    var arg = stmt.getInvokeExp().getArg(i);
                    var argPtr = csManager.getCSVar(context, arg);
                    var param = callee.getIR().getParam(i);
                    var paramPtr = csManager.getCSVar(ct, param);
                    addPFGEdge(argPtr, paramPtr);
                }
            }
            var lvar = stmt.getLValue();
            if (lvar == null)
                return null;
            var lvarPtr = csManager.getCSVar(context, lvar);
            for (Var returnVar : callee.getIR().getReturnVars()) {
                var returnVarPtr = csManager.getCSVar(ct, returnVar);
                addPFGEdge(returnVarPtr, lvarPtr);
            }

            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        AtomicBoolean flag = new AtomicBoolean(false);
        pointerFlowGraph.getSuccsOf(source).forEach(succ -> {
            if (succ.equals(target))
                flag.set(true);
        });
        if (!flag.get()) {
            pointerFlowGraph.addEdge(source, target);
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var ptr = entry.pointer();
            PointsToSet delta = propagate(ptr, entry.pointsToSet());
            if (ptr instanceof CSVar varPtr && !delta.isEmpty()) {
                var var = varPtr.getVar();
                var context = varPtr.getContext();
                for (CSObj csObj : delta) {
                    for (LoadField loadField : var.getLoadFields()) {
                        // y = x.f
                        var lvarPtr = csManager.getCSVar(context, loadField.getLValue());
                        var field = loadField.getFieldRef().resolve();
                        var fieldPtr = csManager.getInstanceField(csObj, field);
                        addPFGEdge(fieldPtr, lvarPtr);
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        // x.f = y
                        var rvarPtr = csManager.getCSVar(context, storeField.getRValue());
                        var field = storeField.getFieldRef().resolve();
                        var fieldPtr = csManager.getInstanceField(csObj, field);
                        addPFGEdge(rvarPtr, fieldPtr);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        // y = x[i]
                        var lvarPtr = csManager.getCSVar(context, loadArray.getLValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(arrayIndex, lvarPtr);
                    }
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        // x[i] = y
                        var rvarPtr = csManager.getCSVar(context, storeArray.getRValue());
                        var arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(rvarPtr, arrayIndex);
                    }
                    processCall(varPtr, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        for (CSObj obj : pointsToSet) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // [x =] o.fun(a1,a2,a3)
        var context = recv.getContext();
        for (Invoke invoke : recv.getVar().getInvokes()) {
            if (invoke.isStatic())
                continue;
            var lvar = invoke.getResult();
            var callee = resolveCallee(recvObj, invoke);
            if (callee == null)
                return;

            var csCallSite = csManager.getCSCallSite(context, invoke);
            var ct = contextSelector.selectContext(csCallSite, recvObj, callee);
            var csCallee = csManager.getCSMethod(ct, callee);
            var thisVarPtr = csManager.getCSVar(ct, callee.getIR().getThis());
            PointsToSet set = PointsToSetFactory.make(recvObj);
            workList.addEntry(thisVarPtr, set);
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke),
                    csCallSite, csCallee))) {
                addReachable(csCallee);
                var invokeExp = invoke.getInvokeExp();
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    var arg = invokeExp.getArg(i);
                    var param = callee.getIR().getParam(i);
                    addPFGEdge(csManager.getCSVar(context, arg), csManager.getCSVar(ct, param));
                }
                if (lvar == null)
                    continue;
                for (Var returnVar : callee.getIR().getReturnVars()) {
                    addPFGEdge(csManager.getCSVar(ct, returnVar), csManager.getCSVar(context, lvar));
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
