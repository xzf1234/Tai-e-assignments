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
        Set<JMethod> remove = new HashSet<>();
        queue.add(entry);
        while (!queue.isEmpty()) {
            JMethod cur = queue.poll();
            if (!remove.contains(cur)) {
                remove.add(cur);
                callGraph.callSitesIn(cur).forEach(site -> {
                    var callees = resolve(site);
                    for (JMethod callee : callees) {
                        callGraph.addReachableMethod(callee);
                        Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(site), site, callee);
                        callGraph.addEdge(edge);
                        queue.add(callee);
                    }
                });
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> set = new HashSet<>();
        JMethod method = callSite.getContainer();
        Subsignature subsignature = method.getSubsignature();
        var call = CallGraphs.getCallKind(callSite);
        switch (call) {
            case STATIC -> set.add(method);
            case SPECIAL -> set.add(dispatch(method.getDeclaringClass(), subsignature));
            case VIRTUAL -> {
                InvokeVirtual virtual = (InvokeVirtual) callSite.getInvokeExp();
                var var = virtual.getBase().getType();
                set.add(dispatch((JClass) var, subsignature)); // base must be class
                getSubClassAndDisPatch(set, (JClass) var, subsignature);
            }
        }
        return set;
    }

    private void getSubClassAndDisPatch(Set<JMethod> set, JClass clazz, Subsignature sig) {
        // find the last class that has no any subclass
        var subc = hierarchy.getDirectSubclassesOf(clazz);
        if (subc.isEmpty())
            set.add(dispatch(clazz, sig));
        else {
            for (JClass sub : subc) {
                getSubClassAndDisPatch(set, sub, sig);
            }
        }

    }


    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null)
            return method;
        else if (jclass.getSuperClass() != null)
            return dispatch(jclass.getSuperClass(), subsignature);
        else
            return null;
    }
}
