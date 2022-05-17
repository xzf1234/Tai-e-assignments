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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me
    public boolean isSource(JMethod method, Type type) {
        for (Source source : config.getSources()) {
            if (source.method().equals(method) && source.type().equals(type))
                return true;
        }
        return false;
    }

    public boolean isSink(JMethod method, int index) {
        for (Sink sink : config.getSinks()) {
            if (sink.method().equals(method) && sink.index() == index)
                return true;
        }
        return false;
    }

    public boolean isBaseToResult(JMethod method, Type type) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(method) &&
                    transfer.type() == type &&
                    transfer.from() == -1 &&
                    transfer.to() == -2)
                return true;
        }
        return false;
    }

    public boolean isArgToBase(JMethod method, int index, Type type) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(method) &&
                    transfer.type().equals(type) &&
                    transfer.from() == index &&
                    transfer.to() == -1)
                return true;
        }
        return false;
    }

    public boolean isArgToResult(JMethod method, int index, Type type) {
        for (TaintTransfer transfer : config.getTransfers()) {
            if (transfer.method().equals(method) &&
                    transfer.type().equals(type) &&
                    transfer.from() == index &&
                    transfer.to() == -2)
                return true;
        }
        return false;
    }

    public Obj markObjAsTaint(Invoke l, Type u) {
        return manager.makeTaint(l, u);
    }

    public boolean isTaintObj(Obj o) {
        return manager.isTaint(o);
    }

    public Context getEmptyContext() {
        return emptyContext;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            var callSite = edge.getCallSite().getCallSite();
            var callSiteContext = edge.getCallSite().getContext();
            var callee = edge.getCallee().getMethod();
            var calleeContext = edge.getCallee().getContext();
            // secret = source()

            for (int i = 0; i < callSite.getInvokeExp().getArgCount(); i++) {
                if (isSink(callee, i)) {
                    var arg = callSite.getInvokeExp().getArg(i);
                    var argPointTo = csManager.getCSVar(callSiteContext, arg).getPointsToSet();
                    for (CSObj csObj : argPointTo) {
                        if (manager.isTaint(csObj.getObject()))
                            taintFlows.add(new TaintFlow((Invoke) csObj.getObject().getAllocation(), callSite, i));
                    }
                }
            }
        });

        return taintFlows;
    }
}
