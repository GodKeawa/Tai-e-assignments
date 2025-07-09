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
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldResolutionFailedException;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;
import java.util.Optional;

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
        // 在实现上我主要考虑在本模块中进行实现,普通的过程中常量分析模块将会完全沿用之前的实现
        // 核心要解决的问题是,过去的常量分析模块只处理简单的赋值语句
        // 查看ConstantPropagation模块,可以看到我们在transferNode时先判断是否是DefinitionStmt
        // 如果发现是,那么就去拿左值,然后将in复制到out,在根据右值的evaluate再次更新out
        // 此时的核心就是evaluate的结果,查看过去的实现,不难发现evaluate只处理了最简单的几种情况
        // 对于field和Array,都会进入默认语句,返回NAC,这导致了不准,我们需要解决这一点

        // 因此我们要做的就是在TransferNonCallNode的时候,处理field和Array(CallNode显然是平凡的)\
        // 对于field和Array,就需要进行别名分析,将所有可能的赋值都传递到位,因此这其实是一个must分析
        // 这也决定了我们如何处理别名关系,即:只要指针分析的结果有重合,就认为是别名,这保证了得到的常量一定是真的
        // 当然因为这样的别名判断过于宽松,又没有上下文敏感性,因此显然也是有一定的不准的

        // 实现上我们采用和科研版一样的策略,进行预处理
        // 核心就是当我们进行Load时,要将所有的Store都meet起来,再传递
        // 对于StaticField,由于没有别名存在,因此是平凡的,可以直接处理
        // 对于InstanceField和Array,都需要进行别名分析

        // 实际上在实现策略上,我们的Fact对所有变量都只保存一个值,因此实际上我们需要进行实时传播
        // 即Store时就要将值传递给所有相应的变量,保证Load时已经是当前分析状态的结果
        // 而Load就只需要Load当前的值即可,worklist自己会找到不动点

        // 先在上面的变量区定义三个Map

        // 进行Static Field的处理
        fieldStoreToLoads = Maps.newMultiMap(); // 初始化Field的map
        // 定义两个辅助map,找到所有的Static Store和Laod
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
                fieldStoreToLoads.put(store, load); // 将所有Store语句可以传递到的Load语句加入Map
            }
        });

        // 处理InstanceField和Array
        MultiMap<Obj, Var> pointedBy = Maps.newMultiMap(); // 指针分析结果处理,转换为对象指向变量的Map
        pta.getVars()                                   // 拿到所有变量
                .stream()
                .filter(v -> !v.getStoreFields().isEmpty() ||   // 保证变量非平凡
                        !v.getLoadFields().isEmpty() ||
                        !v.getStoreArrays().isEmpty() ||
                        !v.getLoadArrays().isEmpty())
                .forEach(v ->                               // 拿到变量指向的所有对象
                        pta.getPointsToSet(v).forEach(obj ->
                                pointedBy.put(obj, v)));        // 反过来让对象指向变量
        arrayStoreToLoads = Maps.newMultiMap(); // 初始化
        arrayLoadToStores = Maps.newMultiMap();

        pointedBy.forEachSet((__, aliases) -> { // 这些变量可能指向同一个对象,因此是别名
            for (Var v : aliases) { // 对别名进行处理
                for (StoreField store : v.getStoreFields()) { // 如果该别名有StoreField语句
                    if (!store.isStatic() && ConstantPropagation.canHoldInt(store.getRValue())) {
                        JField storedField = null;
                        try {
                            storedField = store.getFieldRef().resolve();
                        } catch (FieldResolutionFailedException e) {
                            throw new RuntimeException(e);
                        }
                        JField finalStoredField = storedField; // 拿到StoreField
                        aliases.forEach(u ->                // 检查所有别名的Load
                                u.getLoadFields().forEach(load -> {
                                    JField loadedField = null;
                                    try {
                                        loadedField = load
                                                .getFieldRef().resolve();
                                    } catch (FieldResolutionFailedException e) {
                                        throw new RuntimeException(e);
                                    }
                                    if (finalStoredField.equals(loadedField)) { // 如果field相同,表明该store语句会影响到这个load语句
                                        fieldStoreToLoads.put(store, load); // 加入Map
                                    }
                                })
                        );
                    }
                }
                for (StoreArray store : v.getStoreArrays()) {   // 同理处理Array,但是这里不处理(无法处理)Index,在下面动态处理
                    // 这是因为Array即使Array的对象可能是别名,但Index不一定构成别名(可能相同),这需要更精细的处理
                    // worklist并不保证语句的运行顺序,我们的算法不仅在传播Array[Index]的值,同时还在传播Index的值
                    // 这就是核心问题,任何对象的field都是固定的,该是什么字段就是什么字段,而Array不同
                    // Array的Index同样是一个动态变化的值,随着worklist算法可能会改变
                    // 我们在StoreArray时可以将值传递给当时Index相同的LoadArray
                    // 但是在LoadArray时,我们的Index可能变了,可能接收到不完全的值推送
                    // 比如StoreArray时Index是一个constant : 1,此时这个值会传递给当时Index为1或NAC的Load
                    // 但是如果有一个LoadArray,在上面传播时是1,然后中间的一次worklist操作让它的Index变成了NAC
                    // 那么此时LoadArray接收到的值是不完备的,我们此时只接收到了Index为1的值的推送,如果之前还有为2的,我们还要拿到才行
                    // 因此需要进行动态处理,且进行推拉逻辑,即Store推送改变,Load拉取改变
                    // Load拉取改变并不只会拿到一个Store产生的值,可能拿到很多个,且因为Index的动态性,当前的In的值可能没有被Store完全传播
                    if (ConstantPropagation.canHoldInt(store.getRValue())) {
                        for (Var u : aliases) {
                            for (LoadArray load : u.getLoadArrays()) { // 直接构建Map,对于一个Store语句,将所有Load都加入
                                arrayStoreToLoads.put(store, load); // 这里有双向Map,后面有用
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
        // TODO - finish me DONE
        // 对于CallNode，通常来说在IR上就是一个单纯的invokexxx
        // 此时的Node可以直接传递In到Out，所有精细的分析都由过程间分析的edge处理
        return out.copyFrom(in);
    }

    // Array的传递辅助函数,在这里处理Index的判断
    // 这个函数很关键,因为它实现了值的push和pull操作
    // 我们在下面会在两个地方调用这个函数,操作是不同的
    // 对于LoadArray,我们固定的是load语句,遍历store语句,这意味这我们将所有store的值pull到load中
    // 而对于StoreArray,我们固定的是store语句,遍历load语句,这意味则我们将所有load的值push到store中
    private boolean transferLoadArray(StoreArray store, LoadArray load) {
        Var i = store.getArrayAccess().getIndex(); // 拿到两个语句的Index
        Var j = load.getArrayAccess().getIndex();
        CPFact storeOut = solver.getOutFact(store); // 拿到两个语句的OutFact
        CPFact loadOut = solver.getOutFact(load);
        Value vi = storeOut.get(i); // 拿到Index的值
        Value vj = loadOut.get(j);
        if (!vi.isUndef() && !vj.isUndef()) {
            if (vi.isConstant() && vj.isConstant() && vi.equals(vj) ||
                    vi.isNAC() || vj.isNAC()) {
                // 这部分的逻辑可以参考lab的说明,如果两个之中有一个是UDDEF,那么就不能判断为别名
                // 如果二者都不是UNDEF,其中一个是NAC,那么它们可能是别名,我们就要认为它们是别名
                Var x = store.getRValue();
                Value vx = storeOut.get(x);
                Var y = load.getLValue();
                Value oldVy = loadOut.get(y);
                Value newVy = cp.meetValue(oldVy, vx); // 将Store传递给Load
                return loadOut.update(y, newVy); // 更新,如果有改变则返回true
            }
        }
        return false; // 否则返回false
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me DONE
        // 这里是核心函数,除了这个函数实际上和之前的过程间常量传播函数没有什么区别
        // 在InterSolver中添加了两个辅助函数,逻辑和简单,propagate就是传播值,即加入worklist
        // GetOutFact就是那个意思

        // 这里额外处理我们上面提到的默认常量传播未处理的情况
        if (stmt instanceof LoadArray load) { // LoadArray
            boolean changed = false;
            Var lhs = load.getLValue(); // 拿到赋值的左值
            for (Var inVar : in.keySet()) { // 先把赋值之外的全部从in传递到out
                if (!inVar.equals(lhs)) { // 这里不会修改lhs对应的变量的值,在下面修改
                    changed |= out.update(inVar, in.get(inVar)); // 更新了就会返回true
                }
            }
            for (StoreArray store : arrayLoadToStores.get(load)) { // 拿到该Load的全部Store语句
                // 这里就是和Field的区别,我们在Load之前进行一次全体的store的传递
                // 注意这里是同一个Load,将所有相关的Store进行传递,和下面是不同的
                // 所有Store都会尝试改变Load的OutFact
                changed |= transferLoadArray(store, load); // 尝试将store传递到load,更新了Load的值就返回true
                // transferLoadArray会修改load的OutFact,故解决了上面未修改lhs的问题
            }
            return changed;
        } else if (stmt instanceof StoreArray store) { // StoreArray
            boolean changed = cp.transferNode(store, in, out); // 先进行一次默认传递,因为Store只是将In传递给Out
            // 但是我们要将Store的改变传递给所有的Load,注意transferLoadArray是会修改Load的OutFact的
            for (LoadArray load : arrayStoreToLoads.get(store)) {
                // 这里是同一个store,将store传递给所有相关的Load
                if (transferLoadArray(store, load)) { // 如果store对load产生了改变
                    solver.propagate(load); // 那么这个load的所有后继都需要进行传播
                }
            }
            return changed; // 返回默认传递的结果
        } else if (stmt instanceof LoadField load) { // fieldLoad直接取出来即可,Store时进行了传播
            // 这里Store的传播是完备的,因此Load不需要再把改变pull下来,所有Store都会完全推送它们造成的改变
            boolean changed = false;
            Var lhs = load.getLValue();
            for (Var inVar : in.keySet()) {
                if (!inVar.equals(lhs)) {
                    changed |= out.update(inVar, in.get(inVar));
                }
            }
            return changed;
        }else if (stmt instanceof StoreField store) { // fieldStore需要传播值
            Var var = store.getRValue();
            Value value = in.get(var);
            fieldStoreToLoads.get(store).forEach(load -> { // 找到Store可以影响到的所有Load
                Var lhs = load.getLValue();
                CPFact loadOut = solver.getOutFact(load);
                Value oldV = loadOut.get(lhs);
                Value newV = cp.meetValue(oldV, value);
                if (loadOut.update(lhs, newV)) { // 更新Load的Outfact
                    solver.propagate(load); // 如果有更新就传播到Load的所有后继
                }
            });
            return cp.transferNode(stmt, in, out); // 进行默认的transfer,返回是否改变
        }else {
            return cp.transferNode(stmt, in, out); // 其他情况可以由默认的transfer处理
        }
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me DONE
        // 普通边就是恒等函数
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me DONE
        // CallToReturnEdge是callNode后的边，用来传递本地变量
        // 因此需要kill掉上面可能的赋值语句的左值，该左值会由returnEdge传递、
        // 没有左值就直接传递了
        Stmt src = edge.getSource();
        Optional<LValue> lhs = src.getDef();
        if (lhs.isPresent()) {
            CPFact ret = out.copy();
            ret.remove((Var) lhs.get());
            return ret;
        }
        return out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me DONE
        // CallEdge需要传递参数给过程调用的In
        // CallEdge的source一定是函数调用语句，因此可以拿到一个InvokeExp
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        JMethod callee = edge.getCallee(); // 先拿到函数调用的语句
        CPFact ret = newInitialFact();
        // 不处理InvokeDynamic和调用签名不同的情况
        if (!(invokeExp instanceof InvokeDynamic) &&
                invokeExp.getMethodRef().getSubsignature().equals(callee.getSubsignature())) {
            List<Var> args = invokeExp.getArgs();   // 拿到函数调用时使用的实参
            List<Var> params = callee.getIR().getParams(); // 拿到函数调用的形参
            for (int i = 0; i < args.size(); i++) { // 把实参的值赋给形参
                Var arg = args.get(i);
                Var param = params.get(i);
                if (ConstantPropagation.canHoldInt(param)) {
                    Value argValue = callSiteOut.get(arg);
                    ret.update(param, argValue);
                }
            }
        }

        return ret;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me DONE
        // returnEdge同样处理，将返回的形参赋值给语句的赋值左值实参
        // returnEdge同样保证callsite是Invoke语句
        Var lhs = ((Invoke) edge.getCallSite()).getResult();
        CPFact ret = newInitialFact();
        if (lhs != null && ConstantPropagation.canHoldInt(lhs)) {
            Value retValue = Value.getUndef();
            // 根据约定，返回值可能有多个，因为函数可以有多个return语句
            // API设计使得这个API不会在内部处理多个返回值，实际上如果有多个不同的返回值，基本都是返回NAC
            for (Var v : edge.getReturnVars()) {
                retValue = cp.meetValue(returnOut.get(v), retValue);
            }
            ret.update(lhs, retValue);
        }
        return ret;
    }
}
