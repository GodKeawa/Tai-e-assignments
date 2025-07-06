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
import org.jf.dexlib2.iface.instruction.Instruction;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;
import java.util.Map;
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
        workList = new WorkList(); // WL
        pointerFlowGraph = new PointerFlowGraph(); // PFG
        callGraph = new DefaultCallGraph(); // CG
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
        // TODO - finish me DONE
        // 额外在上面的变量区和initialize中定义了reachableMethod集合，这是必须的
        // Statements集合也设置一下
        // 因为框架没有设置这些变量，我也不知道是否有实现可以不使用这些全局变量进行处理
        // 或许访问者模式可以不需要这些集合，但是我的实现还是需要

        // 这里不仅要处理new和copy，还要处理所有静态字段和静态方法
        if (!callGraph.contains(method)) {
            callGraph.addReachableMethod(method); // 这个方法会处理reachable Stmts
            List<Stmt> Sm = method.getIR().getStmts(); // 这里只处理局部的Stmts
            for (Stmt stmt : Sm) { // 处理所有语句
                if (stmt instanceof New) { // new语句加入worklist
                    Obj obj = heapModel.getObj((New) stmt);
                    Var lhs = ((New) stmt).getLValue();
                    // PFG提供了getVarPtr方法，生成每个Var的Pointer，且这些Pointer对每个Var是独特的，内置一个PointToSet
                    workList.addEntry(pointerFlowGraph.getVarPtr(lhs), new PointsToSet(obj));
                } else if (stmt instanceof Copy) { // copy语句加入一条边
                    Var lhs = ((Copy) stmt).getLValue();
                    Var rhs = ((Copy) stmt).getRValue();
                    addPFGEdge(pointerFlowGraph.getVarPtr(rhs), pointerFlowGraph.getVarPtr(lhs)); // 调用方法加入边
                } else if (stmt instanceof StoreField) { // 处理静态Store T.f = y
                    if (((StoreField) stmt).isStatic()) {
                        JField field = ((StoreField) stmt).getFieldRef().resolve();
                        Var rhs = ((StoreField) stmt).getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(rhs), pointerFlowGraph.getStaticField(field));
                    }
                } else if (stmt instanceof LoadField) { // 处理静态Load x = T.f
                    if (((LoadField) stmt).isStatic()) {
                        JField field = ((LoadField) stmt).getFieldRef().resolve();
                        Var lhs = ((LoadField) stmt).getLValue();
                        addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(lhs));
                    }
                } else if (stmt instanceof Invoke) { // 处理静态方法调用 y = T.m(x)
                    if (((Invoke) stmt).isStatic()) {
                        InvokeExp invokeExp = ((Invoke) stmt).getInvokeExp();
                        JMethod method1 = ((Invoke) stmt).getMethodRef().resolve();
                        addReachable(method1);
                        for (int i = 0; i < method1.getParamCount(); ++i) {
                            Var arg = invokeExp.getArg(i);
                            Var param = method1.getIR().getParam(i);
                            addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                        }
                        Var lhs = ((Invoke) stmt).getLValue(); // invoke语句的赋值左值，可能为null
                        if (lhs != null) {
                            for (Var ret : method1.getIR().getReturnVars()) {
                                addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lhs));
                            }
                        }
                    }
                }
                // 其他语句不处理
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        // 不会访问者模式，学完设计模式再来
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me DONE
        // ADDEdge函数，不仅要考虑加入边，还要进行变量传递，给worklist添加任务
        // 根据函数签名，PFG的addedge函数将会返回图是否变化的flag
        if (pointerFlowGraph.addEdge(source, target)) { // 如果确实加入了一条边
            PointsToSet pointsToSet = source.getPointsToSet(); // PFG提供的Pointer生成函数保证了每个变量都含有一个各自的PointToSet
            if (!pointsToSet.isEmpty()) {
                workList.addEntry(target, pointsToSet); // ADDEdge的默认实现，将target指向的变量传递给source
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
            // 主逻辑，处理所有需要添加的额外边，最后直接处理Call
            if (!delta.isEmpty() && p instanceof VarPtr) {
                for (StoreField stmt : ((VarPtr) p).getVar().getStoreFields()) { // x.f = y
                    if (!stmt.isStatic()) {
                        Var rhs = stmt.getRValue();
                        JField field = stmt.getFieldRef().resolve();
                        for (Obj obj : delta) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(rhs), pointerFlowGraph.getInstanceField(obj, field));
                        }
                    }
                }
                for (LoadField stmt : ((VarPtr) p).getVar().getLoadFields()) { // x = y.f
                    if (!stmt.isStatic()) {
                        Var lhs = stmt.getLValue();
                        JField field = stmt.getFieldRef().resolve();
                        for (Obj obj : delta) {
                            addPFGEdge(pointerFlowGraph.getInstanceField(obj, field),  pointerFlowGraph.getVarPtr(lhs));
                        }
                    }
                }
                for (StoreArray stmt : ((VarPtr) p).getVar().getStoreArrays()) { // x[i] = y
                    Var rhs =  stmt.getRValue();
                    for (Obj obj : delta) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(rhs), pointerFlowGraph.getArrayIndex(obj));
                    }
                }
                for (LoadArray stmt : ((VarPtr) p).getVar().getLoadArrays()) { // x = y[i]
                    Var lhs =stmt.getLValue();
                    for (Obj obj : delta) {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(lhs));
                    }
                }
                for (Obj obj : delta) {
                    processCall(((VarPtr) p).getVar(), obj);
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
        // 不同于ppt给出的实现，delta将会在内部计算并返回出去，return值即为delta
        PointsToSet ret = new PointsToSet();
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me DONE
        // processCall采用标准实现，因为是上下文不敏感的，所以实际上很简单
        // 首先要找到var的所有callsite，这本依赖于我们维护的reachableStmts集合
        // 但本框架提供了相应的API直接获取所有相关的调用，因此暂且先使用API
        // 提供了resolveCallee方法，因此无需dispatch
        for (Invoke invoke : var.getInvokes()) {
            JMethod method = resolveCallee(recv, invoke);
            InvokeExp invokeExp = invoke.getInvokeExp();
            if (method != null) {
                if (!method.isStatic()) { // 非Static Call有this指针，需要传递
                    workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
                }
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))) { // 如果成功加入新边
                    addReachable(method); // 加入reachable Method，并进行参数传递
                    for (int i = 0; i < method.getParamCount(); ++i) {
                        Var arg = invokeExp.getArg(i);
                        Var param = method.getIR().getParam(i);
                        addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                    }
                    Var lhs = invoke.getLValue(); // invoke语句的赋值左值，可能为null
                    if (lhs != null) {
                        for (Var ret : method.getIR().getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(ret), pointerFlowGraph.getVarPtr(lhs));
                        }
                    }
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
