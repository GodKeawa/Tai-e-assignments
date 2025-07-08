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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

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
        csManager = new MapBasedCSManager(); // Context Manager
        callGraph = new CSCallGraph(csManager); // CG
        pointerFlowGraph = new PointerFlowGraph(); // PFG
        workList = new WorkList(); // WL
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        // API to get C.S method
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me DONE
        // 只需要在A5的基础上加上一个平凡的上下文即可,大部分不涉及多个上下文
        // 需要处理Static Call的多个上下文间的变量传递
        if (!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            List<Stmt> Sm = csMethod.getMethod().getIR().getStmts();
            Context context = csMethod.getContext();
            for (Stmt stmt : Sm) {
                if (stmt instanceof New) { // New语句照常加入WL
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
                } else if (stmt instanceof Invoke && ((Invoke) stmt).isStatic()) {
                    InvokeExp invokeExp = ((Invoke) stmt).getInvokeExp();
                    JMethod method = resolveCallee(null, (Invoke) stmt);
                    addReachable(csManager.getCSMethod(context, method));
                    Context Ct = contextSelector.selectContext( // Static Call Select
                            csManager.getCSCallSite(context, (Invoke) stmt), method);
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var arg = invokeExp.getArg(i);
                        Var param = method.getIR().getParam(i);
                        addPFGEdge(csManager.getCSVar(context,arg), csManager.getCSVar(Ct,param));
                    }
                    Var lhs = ((Invoke) stmt).getLValue();
                    if (lhs != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(Ct, ret),csManager.getCSVar(context,lhs));
                        }
                    }
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
        // 依然不使用访问者模式
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me DONE
        // 依然是平凡的,可以完全不改
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
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer p = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = propagate(p, pts);
            if (!delta.isEmpty() && p instanceof CSVar) {
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
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me DONE
        // 同样是平凡的
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
        // TODO - finish me DONE
        // 需要处理上下文,使用接口即可
        Var var = recv.getVar();
        Context c = recvObj.getContext();
        for (Invoke invoke : var.getInvokes()) {
            JMethod method = resolveCallee(recvObj, invoke);
            InvokeExp invokeExp = invoke.getInvokeExp();
            Context Ct = contextSelector.selectContext( // Select Context for Call
                    csManager.getCSCallSite(recv.getContext(), invoke), recvObj, method); // use receiver
            if (method != null) {
                if (!method.isStatic()) {
                    workList.addEntry(
                            csManager.getCSVar(Ct, method.getIR().getThis()),
                            PointsToSetFactory.make(recvObj));
                }
                if (callGraph.addEdge(
                        new Edge<>(CallGraphs.getCallKind(invoke),
                                csManager.getCSCallSite(c, invoke),
                                csManager.getCSMethod(Ct, method)))) {
                    addReachable(csManager.getCSMethod(Ct, method));
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var arg = invokeExp.getArg(i);
                        Var param = method.getIR().getParam(i);
                        addPFGEdge(csManager.getCSVar(c,arg), csManager.getCSVar(Ct,param));
                    }
                    Var lhs = invoke.getLValue();
                    if (lhs != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(Ct, ret),csManager.getCSVar(c,lhs));
                        }
                    }
                }
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

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
