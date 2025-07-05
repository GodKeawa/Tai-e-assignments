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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me DONE
        CPFact fact = newInitialFact(); // 初始化fact表
        cfg.getIR().getParams().forEach(param -> {
            if (canHoldInt(param)) {
                fact.update(param, Value.getNAC());
            }
        });
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me DONE
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me DONE
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(target.get(var), fact.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me DONE
        if (v1.isNAC() || v2.isNAC()) { // 返回NAC
            return Value.getNAC();
        }
        if (v1.isUndef() || v2.isUndef()) { // 返回对方，即使对方也是UNDEF
            if (v1.isUndef()) {
                return v2;
            } else {
                return v1;
            }
        }
        // 必然是两个constant了
        if (v1.equals(v2)) {
            return v1;
        }
        return Value.getNAC();

    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me DONE
        // 因为kill必然是kill那个gen的变量，因此实际上进行一次update即可
        if (stmt instanceof DefinitionStmt) {
            Exp lvalue = ((DefinitionStmt<?, ?>) stmt).getLValue();
            if (lvalue instanceof Var lhs) {
                Exp rhs = ((DefinitionStmt<?, ?>) stmt).getRValue();
                boolean changed = false;
                for (Var inVar : in.keySet()) {
                    if (!inVar.equals(lhs)) {
                        changed |= out.update(inVar, in.get(inVar));
                    }
                }
                return canHoldInt(lhs) ?
                        out.update(lhs, evaluate(rhs, in)) || changed :
                        changed;
            }
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me DONE
        if (exp instanceof IntLiteral) {
            return Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof Var) {
            return canHoldInt((Var) exp) ? in.get((Var) exp) : Value.getNAC();
        } else if (exp instanceof BinaryExp) {
            BinaryExp.Op op = ((BinaryExp) exp).getOperator();
            Value v1 = evaluate(((BinaryExp) exp).getOperand1(), in);
            Value v2 = evaluate(((BinaryExp) exp).getOperand2(), in);
            // handle division-by-zero by returning UNDEF
            if ((op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) &&
                    v2.isConstant() && v2.getConstant() == 0) {
                return Value.getUndef();
            }
            if (v1.isConstant() && v2.isConstant()) {
                int i1 = v1.getConstant();
                int i2 = v2.getConstant();
                return Value.makeConstant(evaluate(op, i1, i2));
            }
            // handle zero * NAC by returning 0
//            if (op == ArithmeticExp.Op.MUL
//                    && (v1.isConstant() && v1.getConstant() == 0 && v2.isNAC() || // 0 * NAC
//                    v2.isConstant() && v2.getConstant() == 0 && v1.isNAC())) { // NAC * 0
//                return Value.makeConstant(0);
//            }
            if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            // 存在一个UNDEF，就是UNDEF
            return Value.getUndef();
        }

        // 特殊表达式，返回NAC，最安全
        return Value.getNAC();
    }

    private static int evaluate(BinaryExp.Op op, int i1, int i2) {
        if (op instanceof ArithmeticExp.Op) {
            return switch ((ArithmeticExp.Op) op) {
                case ADD -> i1 + i2;
                case SUB -> i1 - i2;
                case MUL -> i1 * i2;
                case DIV -> i1 / i2;
                case REM -> i1 % i2;
            };
        } else if (op instanceof BitwiseExp.Op) {
            return switch ((BitwiseExp.Op) op) {
                case OR -> i1 | i2;
                case AND -> i1 & i2;
                case XOR -> i1 ^ i2;
            };
        } else if (op instanceof ConditionExp.Op) {
            return switch ((ConditionExp.Op) op) {
                case EQ -> i1 == i2 ? 1 : 0;
                case NE -> i1 != i2 ? 1 : 0;
                case LT -> i1 < i2 ? 1 : 0;
                case GT -> i1 > i2 ? 1 : 0;
                case LE -> i1 <= i2 ? 1 : 0;
                case GE -> i1 >= i2 ? 1 : 0;
            };
        } else if (op instanceof ShiftExp.Op) {
            return switch ((ShiftExp.Op) op) {
                case SHL -> i1 << i2;
                case SHR -> i1 >> i2;
                case USHR -> i1 >>> i2;
            };
        }
        throw new AnalysisException("Unexpected op: " + op);
    }
}
