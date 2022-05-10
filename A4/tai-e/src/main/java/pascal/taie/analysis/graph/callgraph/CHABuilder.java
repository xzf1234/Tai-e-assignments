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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.exp.InvokeVirtual;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> queue = new LinkedList<>();
        queue.add(entry);
        while (!queue.isEmpty()) {
            JMethod cur = queue.poll();
            if (!callGraph.contains(cur)) {
                callGraph.addReachableMethod(cur);
                if (cur.isAbstract())
                    continue;
                for (Stmt stmt : cur.getIR().getStmts()) {
                    if (stmt instanceof Invoke site) {
                        var callees = resolve(site);
                        for (JMethod callee : callees) {

                            Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(site), site, callee);
                            callGraph.addEdge(edge);
                            queue.add(callee);
                        }
                    }
                }

            }
        }
        return callGraph;
    }

//    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
//        DefaultCallGraph callGraph = new DefaultCallGraph();
//        callGraph.addEntryMethod(entry);
//        // TODO -finish me
//        Queue<JMethod> workList = new LinkedList<JMethod>();
//        workList.add(entry);
//        while(!workList.isEmpty()){
//            JMethod tmpMethod = workList.peek();
//            workList.remove();
//            if(!callGraph.contains(tmpMethod)){
//                callGraph.addReachableMethod(tmpMethod);
//                callGraph.callSitesIn(tmpMethod).forEach(callSite->{
//                            Set<JMethod> Target = resolve(callSite);
//                            for(JMethod method : Target){
//                                //TODO which type?
//                                CallKind kind = CallKind.STATIC;
//                                if(callSite.isVirtual()){
//                                    kind = CallKind.VIRTUAL;
//                                }else if(callSite.isStatic()){
//                                    kind = CallKind.STATIC;
//                                }else if(callSite.isInterface()){
//                                    kind = CallKind.INTERFACE;
//                                }else if(callSite.isSpecial()){
//                                    kind = CallKind.SPECIAL;
//                                }else if(callSite.isDynamic()){
//                                    kind = CallKind.DYNAMIC;
//                                }
//                                if(method!=null) {
//                                    Edge newEdge = new Edge(kind, callSite, method);
//                                    callGraph.addEdge(newEdge);
//                                    workList.add(method);
//                                }
//                            }
//                        }
//                );
//            }
//        }
//
//        return callGraph;
//    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> set = new HashSet<>();
        MethodRef method = callSite.getInvokeExp().getMethodRef();
        Subsignature subsignature = method.getSubsignature();
        JClass clazz = method.getDeclaringClass();
        var call = CallGraphs.getCallKind(callSite);
        switch (call) {
            case STATIC -> set.add(clazz.getDeclaredMethod(subsignature));
            case SPECIAL -> set.add(dispatch(method.getDeclaringClass(), subsignature));
            case VIRTUAL, INTERFACE -> {
//                if (callSite.getLValue() == null)
//                    return set;
                Queue<JClass> queue = new LinkedList<>();
                queue.add(clazz);
                while (!queue.isEmpty()) {
                    JClass cur = queue.poll();
                    var dispatched = dispatch(cur, subsignature);
                    if (dispatched != null)
                        set.add(dispatched);
                    if (cur.isInterface()) {
                        var imples = hierarchy.getDirectImplementorsOf(cur);
                        queue.addAll(imples);
                        var subinter = hierarchy.getDirectSubinterfacesOf(cur);
                        queue.addAll(subinter);
                    } else {
                        var subclass = hierarchy.getDirectSubclassesOf(cur);
                        queue.addAll(subclass);
                    }
                }
//                InvokeVirtual virtual = (InvokeVirtual) callSite.getInvokeExp();
//                var var = virtual.getBase().getType();
//                set.add(dispatch((JClass) var, subsignature)); // base must be class
//                getSubClassAndDisPatch(set, (JClass) var, subsignature);
            }
        }
        return set;
    }


    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null && !method.isAbstract())
            return method;
        else if (jclass.getSuperClass() != null)
            return dispatch(jclass.getSuperClass(), subsignature);
        else
            return null;
    }
}
