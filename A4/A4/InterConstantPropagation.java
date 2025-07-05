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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeDynamic;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.List;
import java.util.Optional;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
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

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me DONE
        // 对于非Call的节点，那就是过程间分析，直接调用原始的转换函数即可
        return cp.transferNode(stmt, in, out);
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
