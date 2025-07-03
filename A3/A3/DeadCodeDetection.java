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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // 不可达代码处理，直接进行逻辑遍历，因为我们拿到了传播的常量，因此可以判断分支不可达的所有情况
        // 对于不可达的分支直接跳过，最后通过Set取差获取不可达代码
        // 无用赋值处理，可以等不可达代码处理完后对可达代码集合进行处理
        // 当然也可以聚合处理
        Set<Stmt> reachableCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Deque<Stmt> worklist = new ArrayDeque<>();
        Stmt entry = cfg.getEntry();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            Stmt work = worklist.pollFirst();
            if (!reachableCode.contains(work)) {
                reachableCode.add(work);
            } else {
                continue;
            }
            if (work instanceof DefinitionStmt) { // 还可能是invoke，但这里不管
                cfg.getOutEdgesOf(work).forEach(edge -> {
                   worklist.add(edge.getTarget());
                });
            } else if (work instanceof If) {
                CPFact fact = constants.getInFact(work);
                ConditionExp exp = ((If) work).getCondition();
                Value result = ConstantPropagation.evaluate(exp, fact);
                if (result.isConstant()) {
                    boolean flag = result.getConstant() != 0;
                    cfg.getOutEdgesOf(work).forEach(outEdge -> {
                        if ((flag && outEdge.getKind() == Edge.Kind.IF_TRUE) || (!flag && outEdge.getKind() == Edge.Kind.IF_FALSE)) {
                            worklist.add(outEdge.getTarget());
                        }
                    });
                } else {
                    cfg.getOutEdgesOf(work).forEach(edge -> {
                        worklist.add(edge.getTarget());
                    });
                }
            } else if (work instanceof SwitchStmt) {
                CPFact fact = constants.getInFact(work);
                Var var = ((SwitchStmt) work).getVar();
                Value value = ConstantPropagation.evaluate(var, fact);
                if (value.isConstant()) {
                    int num = value.getConstant();
                    boolean defaultflag = true;
                    Edge<Stmt> defaultedge = null;
                    for (Edge<Stmt> outEdge : cfg.getOutEdgesOf(work)) {
                        if (outEdge.getKind() == Edge.Kind.SWITCH_CASE) {
                            if (outEdge.getCaseValue() == num) {
                                defaultflag = false;
                                worklist.add(outEdge.getTarget());
                            }
                        } else if (outEdge.getKind() == Edge.Kind.SWITCH_DEFAULT) {
                            defaultedge = outEdge;
                        } else {
                            worklist.add(outEdge.getTarget());
                        }
                    }
                    if (defaultflag && defaultedge != null) {
                        worklist.add(defaultedge.getTarget());
                    }
                } else {
                    cfg.getOutEdgesOf(work).forEach(edge -> {
                        worklist.add(edge.getTarget());
                    });
                }
            } else {
                cfg.getOutEdgesOf(work).forEach(edge -> {
                    worklist.add(edge.getTarget());
                });
            }
        }
        // 现在解决reachable stmt中的无效赋值
        Set<Stmt> uselessDef = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg) {
            if (stmt instanceof DefinitionStmt) {
                Optional<LValue> left = stmt.getDef();
                if (left.isPresent()) {
                    Var var = (Var) left.get();
                    RValue right = ((DefinitionStmt<?, ?>) stmt).getRValue();
                    SetFact<Var> fact = liveVars.getOutFact(stmt);
                    if (!fact.contains(var) && hasNoSideEffect(right)) {
                        uselessDef.add(stmt);
                    }
                }
            }
        }
        for (Stmt stmt : cfg) {
//            System.out.println(stmt.toString() + " <Line>" + stmt.getLineNumber());
            if (!reachableCode.contains(stmt) && stmt.getLineNumber() >= 0) {
                deadCode.add(stmt);
            }
        }
        deadCode.addAll(uselessDef);

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
