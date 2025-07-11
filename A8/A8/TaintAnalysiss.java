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
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;
import java.util.*;

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
    // 辅助函数,判断是否是污点对象
    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    // 处理污点对象的来源问题,从Source的返回值拿到最初的污点对象
    // 同时manager也会记录这个污点对象的最初产生点,即callSite
    public Obj handleTaintSource(Invoke callSite, JMethod callee){
        Type type = callee.getReturnType();
        Source source = new Source(callee, type);
        if(config.getSources().contains(source)){
            return manager.makeTaint(callSite, type); // 传入callSite,记录污点对象的产生位置
        }
        return null;
    }

    // 核心:处理污点对象在各种情况下的转移
    // 污点分析需要考虑的核心的点,即产生信息传递,而非完全的Copy
    // 匹配所有的规则,返回Pair<Var, TaintObj>以供使用
    public Set<Pair<Var, Obj>> handleTaintTransfer(CSCallSite csCallSite, JMethod callee, CSVar base){
        Invoke callSite = csCallSite.getCallSite();
        Var lVar = callSite.getLValue();
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<Pair<Var, Obj>> result = new HashSet<>();
        TaintTransfer transfer;
        if(base != null) {
            // Call (base-to-result)
            Type resultType = callee.getReturnType();
            transfer = new TaintTransfer(callee, TaintTransfer.BASE, TaintTransfer.RESULT, resultType);
            if(config.getTransfers().contains(transfer) && lVar != null){
                Set<CSObj> basePts = ptaResult.getPointsToSet(base);
                basePts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        result.add(new Pair<>(lVar,
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
                    }
                });
            }
            // Call (arg-to-base)
            Type baseType = base.getType();
            List<Var> args = callSite.getInvokeExp().getArgs(); // 需要处理所有arg导致的传递
            for (int i = 0; i < args.size(); i++) {
                Var arg = args.get(i);
                Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
                transfer = new TaintTransfer(callee, i, TaintTransfer.BASE, baseType);
                if (config.getTransfers().contains(transfer)) {
                    argPts.forEach(csObj -> {
                        if(manager.isTaint(csObj.getObject())){
                            result.add(new Pair<>(base.getVar(),
                                    manager.makeTaint(manager.getSourceCall(csObj.getObject()), baseType)));
                        }
                    });
                }
            }
        }
        // Call (arg-to-result)
        List<Var> args = callSite.getInvokeExp().getArgs();
        Type resultType = callee.getReturnType();
        for (int i = 0; i < args.size(); i++) {
            Var arg = args.get(i);
            Set<CSObj> argPts = ptaResult.getPointsToSet(csManager.getCSVar(csCallSite.getContext(), arg));
            transfer = new TaintTransfer(callee, i, TaintTransfer.RESULT, resultType);
            if (config.getTransfers().contains(transfer)) {
                argPts.forEach(csObj -> {
                    if(manager.isTaint(csObj.getObject())){
                        result.add(new Pair<>(lVar,
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
                    }
                });
            }
        }
        return result;
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
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        callGraph.reachableMethods().forEach(csMethod -> { // 拿到所有可达的方法
            callGraph.getCallersOf(csMethod).forEach(csCallSite -> { // 拿到所有方法调用的位置
                Invoke callSite = csCallSite.getCallSite();
                JMethod callee = csMethod.getMethod();
                List<Var> args = callSite.getInvokeExp().getArgs();
                for(int i = 0;i < args.size();i ++){
                    Var arg = args.get(i);
                    Sink sink = new Sink(callee, i);
                    if(config.getSinks().contains(sink)){   // 检查是否是Sink
                        int index = i;
                        result.getPointsToSet(arg).forEach(obj -> { // 检查Sink的所有可能传入对象
                            if(manager.isTaint(obj)){ // 如果是污点
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, index)); // 拿到污点的最初产生位置
                            }
                        });
                    }
                }
            });
        });
        return taintFlows;
    }
}
