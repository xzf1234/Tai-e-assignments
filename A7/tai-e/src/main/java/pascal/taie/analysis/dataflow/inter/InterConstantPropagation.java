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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public Map<FieldRef, Value> staticFieldMap = new HashMap<>();
    public Map<InstanceFieldAccess, Value> instanceFieldMap = new HashMap<>();
    public Map<ArrayAccess, Value> arrayAccessMap = new HashMap<>();

    public Map<Var, Value> arrayIndex = new HashMap<>();

    public PointerAnalysisResult pta;

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt instanceof StoreField storeField) {
            var rvar = storeField.getRValue();
            Value vrvar = in.get(rvar);
            if (storeField.isStatic()) {
                // T.f = x
                var field = storeField.getFieldRef();
                Value fieldV = staticFieldMap.get(field);
                if (fieldV != null)
                    staticFieldMap.put(field, cp.meetValue(fieldV, vrvar));
                else
                    staticFieldMap.put(field, vrvar);
                return out.copyFrom(in);
            } else {
                // x.f = y
                InstanceFieldAccess fieldAccess = (InstanceFieldAccess) storeField.getFieldAccess();
                Value fieldV = instanceFieldMap.get(fieldAccess);
                if (fieldV != null)
                    instanceFieldMap.put(fieldAccess, cp.meetValue(fieldV, vrvar));
                else
                    instanceFieldMap.put(fieldAccess, vrvar);
                return out.copyFrom(in);
            }
        } else if (stmt instanceof LoadField loadField) {
            var lvar = loadField.getLValue();

            if (loadField.isStatic()) {
                // x = T.f
                var field = loadField.getFieldRef();
                Value fieldV = staticFieldMap.get(field);
                CPFact tmp = new CPFact();
                tmp.copyFrom(in);
                if (fieldV != null) {
                    tmp.update(lvar, fieldV);
                }
                return out.copyFrom(tmp);
            } else {
                // y = x.f
                InstanceFieldAccess access = (InstanceFieldAccess) loadField.getFieldAccess();
                Value newV = null;
                for (Map.Entry<InstanceFieldAccess, Value> entry : instanceFieldMap.entrySet()) {
                    if (isInstanceFieldAlias(entry.getKey(), access)) {
                        if (newV == null)
                            newV = entry.getValue();
                        else
                            newV = cp.meetValue(newV, entry.getValue());
                    }
                }
                CPFact tmp = new CPFact();
                tmp.copyFrom(in);
                if (newV != null) {
                    tmp.update(lvar, newV);
                }
                return out.copyFrom(tmp);
            }
        } else if (stmt instanceof StoreArray storeArray) {
            // x[i] = y
            ArrayAccess arrayAccess = storeArray.getArrayAccess();
            var rvar = storeArray.getRValue();
            var vravr = in.get(rvar);
            var index = arrayAccess.getIndex();
            if (in.keySet().contains(rvar)) {
                Value v = arrayAccessMap.get(arrayAccess);
                if (v == null)
                    arrayAccessMap.put(arrayAccess, vravr);
                else
                    arrayAccessMap.put(arrayAccess, cp.meetValue(vravr, v));

                if(in.keySet().contains(index)){
                    Value indexValue = in.get(index);
                    if(indexValue.isConstant())
                        arrayIndex.put(index,indexValue);
                }
            }
            return out.copyFrom(in);

        } else if (stmt instanceof LoadArray loadArray) {
            // y = x[i]
            ArrayAccess arrayAccess = loadArray.getArrayAccess();
            var lvar = loadArray.getLValue();
            Value newV = null;
            for (Map.Entry<ArrayAccess, Value> entry : arrayAccessMap.entrySet()) {
                if (isArrayAlias(arrayAccess, in, entry.getKey())) {
                    if (newV == null)
                        newV = entry.getValue();
                    else
                        newV = cp.meetValue(newV, entry.getValue());
                }
            }
            CPFact tmp = new CPFact();
            tmp.copyFrom(in);
            if (newV != null) {
                tmp.update(lvar, newV);
            }
            return out.copyFrom(tmp);
        }
        return cp.transferNode(stmt, in, out);
    }

    boolean isOverlap(Set<Obj> set1, Set<Obj> set2) {
        for (Obj obj1 : set1) {
            if (set2.contains(obj1))
                return true;
        }
        return false;
    }


    boolean isInstanceFieldAlias(InstanceFieldAccess first, InstanceFieldAccess second) {
        var base_1 = first.getBase();
        var base_2 = second.getBase();
        var field_1 = first.getFieldRef();
        var field_2 = second.getFieldRef();
        return isOverlap(pta.getPointsToSet(base_1), pta.getPointsToSet(base_2))
                && field_1.equals(field_2);
    }

    boolean isArrayAlias(ArrayAccess first, CPFact in, ArrayAccess other) {
        var base_1 = first.getBase();
        Value index_1 = in.get(first.getIndex());
        var base_2 = other.getBase();
        var index = other.getIndex();
        Value index_2;
        if(in.keySet().contains(index))
            index_2 = in.get(other.getIndex());
        else
            index_2 = arrayIndex.get(other.getIndex());
        if(index_2==null)
            return false;
        if (isOverlap(pta.getPointsToSet(base_1), pta.getPointsToSet(base_2))) {
            if (index_1 == Value.getUndef() || index_2 ==Value.getUndef() ) {
                return false;
            } else {
                if (index_1.isConstant() && index_2.isConstant()) {
                    return index_1.getConstant() == index_2.getConstant();
                } else
                    return true;
            }

        } else
            return false;
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact res = out.copy();
        Invoke src = (Invoke) edge.getSource();
        if (src.getLValue() != null) {
            Var lvar = src.getLValue();
            res.remove(lvar);
            return res;
        } else
            return out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        InvokeExp exp = ((Invoke) edge.getSource()).getInvokeExp();
        List<Var> args = exp.getArgs();
        Stmt target = edge.getTarget();
        var ir = icfg.getContainingMethodOf(target).getIR();
        CPFact out = new CPFact();
        for (int i = 0; i < args.size(); i++) {
            if (ConstantPropagation.canHoldInt(args.get(i))) {
                Var v = args.get(i);
                var value = callSiteOut.get(v);
                if (value != null) {
                    out.update(ir.getParam(i), value);
                }
                arrayIndex.put(ir.getParam(i),value);
            }
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var target = (Invoke) edge.getCallSite();
        CPFact res = new CPFact();
        var lvar = target.getResult();
        var vars = edge.getReturnVars();
        if (lvar == null)
            return res;
        Value fin = null;
        for (Var var : vars) {
            var v = returnOut.get(var);
            if (ConstantPropagation.canHoldInt(lvar) && ConstantPropagation.canHoldInt(var)) {
                if (fin == null)
                    fin = v;
                else {
                    fin = cp.meetValue(fin, v);
                }
            }
        }
        if (fin == null)
            return res;
        else {
            res.update(lvar, fin);
            return res;
        }
    }
}

