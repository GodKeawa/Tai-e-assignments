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
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldResolutionFailedException;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private MultiMap<StoreField, LoadField> fieldStoreToLoads;
    private MultiMap<StoreArray, LoadArray> arrayStoreToLoads;
    private MultiMap<LoadArray, StoreArray> arrayLoadToStores;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here

        fieldStoreToLoads = Maps.newMultiMap();
        MultiMap<JField, StoreField> staticStores = Maps.newMultiMap();
        MultiMap<JField, LoadField> staticLoads = Maps.newMultiMap();
        for (Stmt s : icfg) {
            if (s instanceof StoreField store) {
                if (store.isStatic() && ConstantPropagation.canHoldInt(store.getRValue())) {
                    try {
                        staticStores.put(store.getFieldRef().resolve(), store);
                    } catch (FieldResolutionFailedException e) {
                        throw new RuntimeException(e);
                    }
                }
            }
            if (s instanceof LoadField load) {
                if (load.isStatic() && ConstantPropagation.canHoldInt(load.getLValue())) {
                    try {
                        staticLoads.put(load.getFieldRef().resolve(), load);
                    } catch (FieldResolutionFailedException e) {
                        throw new RuntimeException(e);
                    }
                }
            }
        }
        staticStores.forEach((field, store) -> {
            for (LoadField load : staticLoads.get(field)) {
                fieldStoreToLoads.put(store, load);
            }
        });

        MultiMap<Obj, Var> pointedBy = Maps.newMultiMap();
        pta.getVars()
                .stream()
                .filter(v -> !v.getStoreFields().isEmpty() ||
                        !v.getLoadFields().isEmpty() ||
                        !v.getStoreArrays().isEmpty() ||
                        !v.getLoadArrays().isEmpty())
                .forEach(v ->
                        pta.getPointsToSet(v).forEach(obj ->
                                pointedBy.put(obj, v)));
        arrayStoreToLoads = Maps.newMultiMap();
        arrayLoadToStores = Maps.newMultiMap();
        pointedBy.forEachSet((__, aliases) -> {
            for (Var v : aliases) {
                for (StoreField store : v.getStoreFields()) {
                    if (!store.isStatic() && ConstantPropagation.canHoldInt(store.getRValue())) {
                        JField storedField = null;
                        try {
                            storedField = store.getFieldRef().resolve();
                        } catch (FieldResolutionFailedException e) {
                            throw new RuntimeException(e);
                        }
                        JField finalStoredField = storedField;
                        aliases.forEach(u ->
                                u.getLoadFields().forEach(load -> {
                                    JField loadedField = null;
                                    try {
                                        loadedField = load
                                                .getFieldRef().resolve();
                                    } catch (FieldResolutionFailedException e) {
                                        throw new RuntimeException(e);
                                    }
                                    if (finalStoredField.equals(loadedField)) {
                                        fieldStoreToLoads.put(store, load);
                                    }
                                })
                        );
                    }
                }
                for (StoreArray store : v.getStoreArrays()) {
                    if (ConstantPropagation.canHoldInt(store.getRValue())) {
                        for (Var u : aliases) {
                            for (LoadArray load : u.getLoadArrays()) {
                                arrayStoreToLoads.put(store, load);
                                arrayLoadToStores.put(load, store);
                            }
                        }
                    }
                }
            }
        });
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
        return stmt.accept(new StmtVisitor<>() {

            @Override
            public Boolean visit(LoadArray load) {
                boolean changed = false;
                Var lhs = load.getLValue();
                // do not propagate lhs
                for (Var inVar : in.keySet()) {
                    if (!inVar.equals(lhs)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                for (StoreArray store : arrayLoadToStores.get(load)) {
                    changed |= transferLoadArray(store, load);
                }
                return changed;
            }

            @Override
            public Boolean visit(StoreArray store) {
                boolean changed = cp.transferNode(store, in, out);
                for (LoadArray load : arrayStoreToLoads.get(store)) {
                    if (transferLoadArray(store, load)) {
                        solver.propagate(load);
                    }
                }
                return changed;
            }

            private boolean transferLoadArray(StoreArray store, LoadArray load) {
                // suppose that
                // store is a[i] = x;
                // load is y = b[j];
                Var i = store.getArrayAccess().getIndex();
                Var j = load.getArrayAccess().getIndex();
                CPFact storeOut = solver.getOutFact(store);
                CPFact loadOut = solver.getOutFact(load);
                Value vi = storeOut.get(i);
                Value vj = loadOut.get(j);
                if (!vi.isUndef() && !vj.isUndef()) {
                    if (vi.isConstant() && vj.isConstant() && vi.equals(vj) ||
                            vi.isNAC() || vj.isNAC()) {
                        Var x = store.getRValue();
                        Value vx = storeOut.get(x);
                        Var y = load.getLValue();
                        Value oldVy = loadOut.get(y);
                        Value newVy = cp.meetValue(oldVy, vx);
                        return loadOut.update(y, newVy);
                    }
                }
                return false;
            }

            @Override
            public Boolean visit(LoadField load) {
                boolean changed = false;
                Var lhs = load.getLValue();
                // do not propagate lhs
                for (Var inVar : in.keySet()) {
                    if (!inVar.equals(lhs)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                return changed;
            }

            @Override
            public Boolean visit(StoreField store) {
                Var var = store.getRValue();
                Value value = in.get(var);
                fieldStoreToLoads.get(store).forEach(load -> {
                    // propagate stored value to aliased loads
                    Var lhs = load.getLValue();
                    CPFact loadOut = solver.getOutFact(load);
                    Value oldV = loadOut.get(lhs);
                    Value newV = cp.meetValue(oldV, value);
                    if (loadOut.update(lhs, newV)) {
                        solver.propagate(load);
                    }
                });
                return cp.transferNode(stmt, in, out);
            }

            @Override
            public Boolean visitDefault(Stmt stmt) {
                return cp.transferNode(stmt, in, out);
            }
        });
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        Invoke invoke = (Invoke) edge.getSource();
        Var lhs = invoke.getResult();
        if (lhs != null) {
            CPFact result = out.copy();
            result.remove(lhs);
            return result;
        } else {
            return out;
        }
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        JMethod callee = edge.getCallee();
        CPFact result = newInitialFact();
        if (!(invokeExp instanceof InvokeDynamic) &&
                invokeExp.getMethodRef().getSubsignature()
                        .equals(callee.getSubsignature())) {
            // skip invokedynamic and the special call edges
            // whose call-site subsignature does not equal to callee's
            List<Var> args = invokeExp.getArgs();
            List<Var> params = callee.getIR().getParams();
            for (int i = 0; i < args.size(); ++i) {
                Var arg = args.get(i);
                Var param = params.get(i);
                if (ConstantPropagation.canHoldInt(param)) {
                    Value argValue = callSiteOut.get(arg);
                    result.update(param, argValue);
                }
            }
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        Var lhs = ((Invoke) edge.getCallSite()).getResult();
        CPFact result = newInitialFact();
        if (lhs != null && ConstantPropagation.canHoldInt(lhs)) {
            Value retValue = edge.getReturnVars()
                    .stream()
                    .map(returnOut::get)
                    .reduce(Value.getUndef(), cp::meetValue);
            result.update(lhs, retValue);
        }
        return result;
    }
}
