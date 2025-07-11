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
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private Map<CSVar, Set<Invoke>> possibleTaintTransfers; // 需要一个记录函数调用的Map

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.possibleTaintTransfers = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    // frame from A6
    private void processSingleCall(CSCallSite callSite, CSMethod method){
        Invoke invoke = callSite.getCallSite();
        InvokeExp invokeExp = invoke.getInvokeExp();

        // Taint Analysis,需要处理污点来源
        Obj obj = taintAnalysis.handleTaintSource(invoke, method.getMethod()); // 拿到污点对象
        Var lVar = callSite.getCallSite().getLValue(); // 拿到左值,即赋值的目标对象
        if(obj != null && lVar != null){
            CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), obj);
            Pointer ptr = csManager.getCSVar(callSite.getContext(), lVar);
            workList.addEntry(ptr, PointsToSetFactory.make(csObj)); // 传递
        }

        // same as A6
        Context c = callSite.getContext();
        Context Ct = method.getContext();
        if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), callSite, method))) {
            addReachable(method);
            List<Var> params = method.getMethod().getIR().getParams();
            for(int i = 0;i < invokeExp.getArgCount(); ++i) {
                addPFGEdge(
                        csManager.getCSVar(c, invokeExp.getArg(i)),
                        csManager.getCSVar(Ct, params.get(i))
                );
            }
            if(invoke.getLValue() != null){
                method.getMethod().getIR().getReturnVars().forEach(ret -> {
                    addPFGEdge(
                            csManager.getCSVar(Ct, ret),
                            csManager.getCSVar(c, invoke.getLValue())
                    );
                });
            }
        }
    }
    // 新增,处理污点传递的函数,调用taintAnalysis中的方法进行处理
    private void transferTaint(CSCallSite csCallSite, JMethod callee, CSVar base){
        // 调用分析函数获取所有变量和要传递给它们的Obj
        taintAnalysis.handleTaintTransfer(csCallSite, callee, base).forEach(varObjPair -> {
            Var var = varObjPair.first();
            Obj obj = varObjPair.second();
            CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), obj);
            Pointer ptr = csManager.getCSVar(csCallSite.getContext(), var);
            workList.addEntry(ptr, PointsToSetFactory.make(csObj));
        });
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        // frame from A6
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            List<Stmt> Sm = csMethod.getMethod().getIR().getStmts();
            Context context = csMethod.getContext();
            for (Stmt stmt : Sm) {
                if (stmt instanceof New) { // 普通语句非函数调用,均无改变
                    Obj obj = heapModel.getObj((New) stmt);
                    Var lhs = ((New) stmt).getLValue();
                    Context Ct = contextSelector.selectHeapContext(csMethod, obj);
                    workList.addEntry(
                            csManager.getCSVar(context, lhs),
                            PointsToSetFactory.make(csManager.getCSObj(Ct, obj))
                    );
                } else if (stmt instanceof Copy) { // 剩下的加边即可
                    Var lhs = ((Copy) stmt).getLValue();
                    Var rhs = ((Copy) stmt).getRValue();
                    addPFGEdge(csManager.getCSVar(context,rhs), csManager.getCSVar(context,lhs));
                } else if (stmt instanceof StoreField && ((StoreField) stmt).isStatic()) {
                    JField field = ((StoreField) stmt).getFieldRef().resolve();
                    Var rhs = ((StoreField) stmt).getRValue();
                    addPFGEdge(csManager.getCSVar(context, rhs), csManager.getStaticField(field));
                } else if (stmt instanceof LoadField && ((LoadField) stmt).isStatic()) {
                    JField field = ((LoadField) stmt).getFieldRef().resolve();
                    Var lhs = ((LoadField) stmt).getLValue();
                    addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context,lhs));
                } else if (stmt instanceof Invoke) { // 需要为污点分析进行处理
                    if (((Invoke) stmt).isStatic()) {
                        JMethod method = resolveCallee(null, (Invoke) stmt);
                        CSCallSite callSite = csManager.getCSCallSite(context, (Invoke) stmt);
                        Context Ct = contextSelector.selectContext(callSite, method);
                        processSingleCall(callSite, csManager.getCSMethod(Ct, method));
                        transferTaint(callSite, method, null); // 添加污点传播
                    }
                    // 额外处理逻辑,对于所有函数调用,都要处理可能的污点传播,考虑所有的传入对象(this也会包含其中)和对应的调用点
                    // 需要再次进行遍历,因为每次调用的context可能不同
                    csMethod.getMethod().getIR().getStmts().forEach(stmt1 -> {
                        if(stmt1 instanceof Invoke invoke){
                            invoke.getInvokeExp().getArgs().forEach(arg -> {
                                CSVar var = csManager.getCSVar(context, arg); // 传入当前context下的变量
                                Set<Invoke> invokes = possibleTaintTransfers.getOrDefault(var, new HashSet<>());
                                invokes.add(invoke);
                                possibleTaintTransfers.put(var, invokes);
                            });
                        }
                    });
                }
                // 其他语句不处理
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
        // 照例不实现
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        // from A6 no change
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pointsToSet = source.getPointsToSet();
            if (!pointsToSet.isEmpty()) {
                workList.addEntry(target, pointsToSet);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        // frame from A6
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer p = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(p, pts);
            if (!delta.isEmpty() && p instanceof CSVar) { // 一般情况同样是不变的
                Context c = ((CSVar) p).getContext();
                for (StoreField stmt : ((CSVar) p).getVar().getStoreFields()) {
                    if (!stmt.isStatic()) {
                        Var rhs = stmt.getRValue();
                        JField field = stmt.getFieldRef().resolve();
                        for (CSObj obj : delta) {
                            addPFGEdge(csManager.getCSVar(c,rhs), csManager.getInstanceField(obj, field));
                        }
                    }
                }
                for (LoadField stmt : ((CSVar) p).getVar().getLoadFields()) {
                    if (!stmt.isStatic()) {
                        Var lhs = stmt.getLValue();
                        JField field = stmt.getFieldRef().resolve();
                        for (CSObj obj : delta) {
                            addPFGEdge(csManager.getInstanceField(obj, field), csManager.getCSVar(c,lhs));
                        }
                    }
                }
                for (StoreArray stmt : ((CSVar) p).getVar().getStoreArrays()) {
                    Var rhs = stmt.getRValue();
                    for (CSObj obj : delta) {
                        addPFGEdge(csManager.getCSVar(c, rhs), csManager.getArrayIndex(obj));
                    }
                }
                for (LoadArray stmt : ((CSVar) p).getVar().getLoadArrays()) {
                    Var lhs = stmt.getLValue();
                    for (CSObj obj : delta) {
                        addPFGEdge(csManager.getArrayIndex(obj), csManager.getCSVar(c,lhs));
                    }
                }
                for (CSObj obj : delta) {
                    processCall((CSVar) p, obj);
                    // TaintTransfer
                    if(taintAnalysis.isTaint(obj.getObject())){
                        possibleTaintTransfers.getOrDefault((CSVar) p, new HashSet<>()).forEach(invoke -> {
                            CSCallSite csCallSite = csManager.getCSCallSite(c, invoke);
                            if(invoke.getInvokeExp() instanceof InvokeInstanceExp exp){
                                CSVar recv = csManager.getCSVar(c, exp.getBase());
                                result.getPointsToSet(recv).forEach(recvObj -> {
                                    JMethod callee = resolveCallee(recvObj, invoke);
                                    transferTaint(csCallSite, callee, recv);
                                });
                            }else{
                                JMethod callee = resolveCallee(null, invoke);
                                transferTaint(csCallSite, callee, null);
                            }
                        });
                    }
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
        // from A6 no change
        PointsToSet ret = PointsToSetFactory.make();
        if (!pointsToSet.isEmpty()) {
            pointsToSet.getObjects().forEach(obj -> { // pt(n) U= pts
                if (pointer.getPointsToSet().addObject(obj)) { // addObject具有flag返回值
                    ret.addObject(obj);
                }
            });
        }
        if (!ret.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> { // 把pointer的后继也全部更新，加上pts
                workList.addEntry(succ, ret);
            });
        }
        return ret;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        // frame from A6
        Var var = recv.getVar();
        Context c = recv.getContext();
        for (Invoke invoke : var.getInvokes()) {
            JMethod method = resolveCallee(recvObj, invoke);
            CSCallSite callSite = csManager.getCSCallSite(c, invoke);
            Context Ct = contextSelector.selectContext( // Select Context for Call
                    callSite, recvObj, method); // use receiver
            if (method != null) {
                if (!method.isStatic()) {
                    workList.addEntry(
                            csManager.getCSVar(Ct, method.getIR().getThis()),
                            PointsToSetFactory.make(recvObj));
                }
                processSingleCall(callSite, csManager.getCSMethod(Ct, method));
                transferTaint(callSite, method, recv); // Taint Analysis
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
