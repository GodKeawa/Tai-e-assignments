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
import pascal.taie.util.collection.Sets;

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
        // TODO - finish me DONE
        // Your task is to recognize dead code in ir and add it to deadCode
        // 不可达代码处理，直接进行逻辑遍历，因为我们拿到了传播的常量，因此可以判断分支不可达的所有情况
        // 对于不可达的分支直接跳过，最后通过Set取差获取不可达代码
        // 无用赋值处理，可以等不可达代码处理完后对可达代码集合进行处理
        // 当然也可以聚合处理
        Set<Stmt> reachableCode = Sets.newSet(cfg.getNumberOfNodes());
        Queue<Stmt> worklist = new ArrayDeque<>();
        worklist.add(cfg.getEntry());
        while (!worklist.isEmpty()) {
            Stmt stmt = worklist.remove();
            if (!reachableCode.contains(stmt)) {
                reachableCode.add(stmt);
            } else {
                continue;
            }
            cfg.getOutEdgesOf(stmt).forEach(edge -> {
                Stmt src = edge.getSource();
                if (src instanceof If ifStmt) {
                    Value cond = ConstantPropagation.evaluate(
                            ifStmt.getCondition(), constants.getInFact(ifStmt));
                    if (cond.isConstant()) {
                        int v = cond.getConstant();
                        if (v == 0 && edge.getKind() == Edge.Kind.IF_FALSE ||
                                v == 1 && edge.getKind() == Edge.Kind.IF_TRUE) {
                            worklist.add(edge.getTarget());
                        }
                    } else {
                        worklist.add(edge.getTarget());
                    }
                } else if (src instanceof SwitchStmt switchStmt) {
                    Value condV = ConstantPropagation.evaluate(
                            switchStmt.getVar(), constants.getInFact(switchStmt));
                    if (condV.isConstant()) {
                        int v = condV.getConstant();
                        if (edge.isSwitchCase()) {
                            if (v == edge.getCaseValue()) {
                                worklist.add(edge.getTarget());
                            }
                        } else { // default case
                            if (switchStmt.getCaseValues()
                                    .stream()
                                    .noneMatch(x -> x == v)) {
                                worklist.add(edge.getTarget());
                            }
                        }
                    } else {
                        worklist.add(edge.getTarget());
                    }
                } else {
                    worklist.add(edge.getTarget());
                }
            });
        }

        for (Stmt stmt : ir) {
            if (stmt instanceof AssignStmt<?, ?> assign) {
                if (assign.getLValue() instanceof Var lhs) {
                    if (!liveVars.getOutFact(assign).contains(lhs) &&
                            hasNoSideEffect(assign.getRValue())) {
                        deadCode.add(stmt);
                    }
                }
            }
        }

        if (reachableCode.size() < cfg.getNumberOfNodes()) {
            // this means that some nodes are not reachable during traversal
            for (Stmt s : ir) {
                if (!reachableCode.contains(s)) {
                    deadCode.add(s);
                }
            }
        }
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
