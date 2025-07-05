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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me DONE
        Queue<JMethod> worklist = new ArrayDeque<>(); // worklist
        worklist.add(entry);
        // Reachable method内置在DefaultCallGraph中了
        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (!callGraph.contains(method)) {
                callGraph.addReachableMethod(method);
                for (Invoke callsite : callGraph.getCallSitesIn(method)) {
                    Set<JMethod> methods = resolve(callsite);
                    worklist.addAll(methods);
                    for  (JMethod m : methods) {
                        callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callsite), callsite, m));
                    }
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me DONE
        // 按照callsite的类型进行分类讨论
        Set<JMethod> methods = new HashSet<>(); // 初始时为空
        CallKind kind = CallGraphs.getCallKind(callSite);
        MethodRef methodref = callSite.getMethodRef();
        Subsignature subsignature = methodref.getSubsignature();
        JClass clazz = methodref.getDeclaringClass();
        switch (kind) {
            case STATIC -> { // Static方法就是对应类中的方法
                methods.add(clazz.getDeclaredMethod(subsignature));
            }
            case SPECIAL -> { // Special包含自身类的一些方法和父类中的方法，因此需要dispatch，保证有一个结果，不用处理null
                methods.add(dispatch(clazz, subsignature));
            }
            case VIRTUAL, INTERFACE -> { // Virtual和Interface包含整个类继承树上的方法
                Queue<JClass> queue = new ArrayDeque<>(); // 使用一个Queue进行遍历
                queue.add(clazz);
                while (!queue.isEmpty()) {
                    JClass jclass = queue.poll();
                    JMethod method = dispatch(jclass, subsignature); // 总之先dispatch
                    if (method != null && !method.isAbstract()) {
                        methods.add(method);
                    }
                    if (jclass.isInterface()) { // 接口既要找继承该接口的接口，也要找直接实现该接口的类
                        queue.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                        queue.addAll(hierarchy.getDirectImplementorsOf(jclass));
                    } else {
                        // 如果是一个有效的类，直接找子类即可
                        queue.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                }
            }
        }

        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me DONE
        // 在类中寻找指定的方法，如果没有，就递归地到父类中去找，如果没有父类，那么就返回null
        // 要考虑抽象方法
        if (jclass == null) { // 递归找父类时可能没有父类，此时返回的是null
            return null;
        } else { // 类有效
            JMethod method = jclass.getDeclaredMethod(subsignature);
            if (method != null && !method.isAbstract()) {
                return jclass.getDeclaredMethod(subsignature); // 如果类里有该方法且不是抽象方法
            } else {
                return dispatch(jclass.getSuperClass(), subsignature); // 没有则递归到父类里找
            }
        }
    }
}
