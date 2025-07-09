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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        Set<Node> entryNodes = icfg.entryMethods()
                .map(icfg::getEntryOf)
                .collect(Collectors.toSet());
        entryNodes.forEach(entry -> {
            result.setInFact(entry, analysis.newBoundaryFact(entry));
            result.setOutFact(entry, analysis.newBoundaryFact(entry));
        });
        icfg.forEach(node -> {
            if (entryNodes.contains(node)) {
                return;
            }
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        });
    }

    private void doSolve() {
        // TODO - finish me DONE
        workList = new SetQueue<>();
        icfg.forEach(node -> {
            workList.add(node);
        });
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            Fact in = result.getInFact(node); // 拿到节点的In
            icfg.getInEdgesOf(node).forEach(edge -> { // 查看节点的所有InEdge
                Fact predout = result.getOutFact(edge.getSource()); // 拿到InEdge的源节点的Out
                analysis.meetInto(analysis.transferEdge(edge, predout), in); // 进行边转换，然后合并到In里
            });
            Fact out = result.getOutFact(node);
            if (analysis.transferNode(node, in, out)) { // 进行节点转换，看是否有改变
                workList.addAll(icfg.getSuccsOf(node)); // 加入所有后继
            }
        }
    }

    void propagate(Node node) {
        workList.addAll(icfg.getSuccsOf(node));
    }

    Fact getOutFact(Node node) {
        return result.getOutFact(node);
    }
}