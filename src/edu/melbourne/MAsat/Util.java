/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.Symbol;
import gurobi.GRB;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

/**
 *
 * @author kafle
 */
public class Util {

    public static long modulo_m() {
        return (long) Math.pow(2, Main.INT_WIDTH);

    }

    public static long modulo_m(int m) {
        return (long) Math.pow(2, m);
    }

    public static long max_pos(int num) {
        return (long) Math.pow(2, num) - 1; //unsigned
    }

    public static long min_neg(int num) {
        return 0;
        //return -((long) Math.pow(2, Main.INT_WIDTH - 1));//signed
    }

    public static long max_pos() {
        //return (long) Math.pow(2, Main.INT_WIDTH-1) - 1; //signed
        //return 15;
        return (long) Math.pow(2, Main.INT_WIDTH) - 1; //unsigned
    }

    public static long min_neg() {
        return 0;
        //return -((long) Math.pow(2, Main.INT_WIDTH - 1));//signed
    }

    public static HashSet<IntExpr> collectIntVars(Expr e) {
        HashSet<IntExpr> set = new HashSet<>();
        collectIntVars1(e, set);
        // System.out.println("the var set "+set);
        return set;
    }

    public static void collectIntVars1(Expr e, HashSet<IntExpr> set) {
        if (e.isConst() && e.isInt()) { //isConstant gives var and isInt gives integer sort
            set.add((IntExpr) e);
        } else if (e.isIntNum()) {
        } else if (e.isApp() && e.getNumArgs() > 0) {
            Expr[] exprs = e.getArgs();
            for (int i = 0; i < exprs.length; i++) {
                collectIntVars1(exprs[i], set);
            }
        } else {
            //nothing
        }
    }

    public static HashSet<BvVariable> collectBvVars(Expr e, Context ctx) {
//        System.out.println("collecting vars from "+e);
        HashSet<BvVariable> set = new HashSet<>();
        collectBVVars1(e, set, ctx);
//         System.out.println("the var set =======||||======"+set.size());
        return set;
    }

    public static void collectBVVars1(Expr e, HashSet<BvVariable> set, Context ctx) {
        if (e.isConst() && e.isBV()) { //isConstant gives var and isInt gives integer sort
            set.add(new BvVariable(ctx.mkSymbol(e.toString()), ((BitVecExpr) e).getSortSize()));
            // System.out.println("the size "+set.size());
        } else if (isBVBooleanOperation(e)) {
            Expr[] exprs = e.getArgs();
            for (int i = 0; i < exprs.length; i++) {
                collectBVVars1(exprs[i], set, ctx);
            }
        } else if (isBVArithOperation(e)) {
            Expr[] exprs = e.getArgs();
            for (int i = 0; i < exprs.length; i++) {
                collectBVVars1(exprs[i], set, ctx);
            }
        } else { //boolean variable case, not dealt now
        }
    }

    public static HashSet<BvVariable> varUnion(HashSet<BvVariable> set1, HashSet<BvVariable> set2) {
        for (BvVariable ie : set2) {
            set1.add(ie);
        }
        return set1;
    }

    public static boolean isBVBooleanOperation(Expr beBV) {
        return (beBV.isEq() || beBV.isBVULE() || beBV.isBVULT() || beBV.isBVUGT() || beBV.isBVUGE());
    }

    public static boolean isBVArithOperation(Expr bvArith) {
        return (bvArith.isBVAdd() || bvArith.isBVSub() || bvArith.isBVUMinus() || bvArith.isBVMul() || bvArith.isBVShiftLeft() || bvArith.isBVShiftRightArithmetic() || bvArith.isBVExtract() || bvArith.isBVConcat());
    }

    public static long getModulo(IntNum e) {
        return (e.getInt64() % Util.modulo_m());
    }

    public static long getModuloM(IntNum e, int modulo) {
        return (e.getInt64() % Util.modulo_m(modulo));
    }

    /**
     * with explict bounds for the variable
     */
    public static void createZ3GRBVarMap(GRBModel model, HashSet<BvVariable> z3Vars, HashMap<IntExpr, GRBVar> z3GRBVarMap, Context ctx) {
        int varSortSize;
        IntExpr intExpr;
        GRBVar grbVar;
        for (BvVariable ie : z3Vars) {
            varSortSize = ie.getSortSize();
            intExpr = ctx.mkIntConst(ie.getName());
            grbVar = createGRBVar(model, intExpr, min_neg(varSortSize), max_pos(varSortSize));
            if (!z3GRBVarMap.containsKey(intExpr)) {
                z3GRBVarMap.put(intExpr, grbVar);
            }
        }
    }

    public static GRBVar createGRBVar(GRBModel model, IntExpr z3Var, double lower, double upper) {
        GRBVar var = null;
        String varName = z3Var.getSExpr().trim();
        try {
            var = model.getVarByName(varName);
            if (var == null) {
                var = model.addVar(lower, upper, 0, GRB.INTEGER, varName);
            }
        } catch (GRBException ex) {
            try {
                var = model.addVar(lower, upper, 0, GRB.INTEGER, varName);
            } catch (GRBException ex1) {
                ex1.printStackTrace();
            }
        }
        return var;
    }

    public GRBModel addConstrsGRB(BoolExpr be, GRBModel model, String id, HashMap<IntExpr, GRBVar> z3GRBVarMap) {//be is an arith constraint
        ArrayList<Expr> exprsAl = collectConjuncts(be);
        //System.out.println("id is ==========   "+id);
        Expr[] exprs = exprsAl.toArray(new Expr[exprsAl.size()]);
        for (int i = 0; i < exprs.length; i++) {
            String idNew = id + "__r__" + i;
            // System.out.println("added id formula ============================= "+idNew+" "+exprs[i]);
            model = addAConstrGRB((BoolExpr) exprs[i], model, idNew, z3GRBVarMap);
        }
        return model;
    }

    public ArrayList<Expr> collectConjuncts(BoolExpr be) {
        Expr[] exprList;
        ArrayList<Expr> exprs = new ArrayList<>();
        if (be.isAnd()) {
            exprList = be.getArgs();
            for (int i = 0; i < exprList.length; i++) {
                exprs = mergeArrayL(exprs, collectConjuncts((BoolExpr) exprList[i]));
            }
        } else if (!be.isTrue()) {
            exprs.add(be);
        }
        return exprs;
    }

    public ArrayList<Expr> mergeArrayL(ArrayList<Expr> l1, ArrayList<Expr> l2) {
        for (int i = 0; i < l2.size(); i++) {
            l1.add(l2.get(i));
        }
        return l1;
    }

    public GRBModel addListConstrsGRB(ArrayList<BoolExpr> constraints, GRBModel model, String id, HashMap<IntExpr, GRBVar> z3GRBVarMap) {//be is an arith constraint
        //System.out.println("id is ==========   "+id);
        for (int i = 0; i < constraints.size(); i++) {
            String idNew = id + "__r__" + i;
//             System.out.println("added id formula ============================= "+idNew+" "+constraints.get(i));
            model = addAConstrGRB((BoolExpr) constraints.get(i), model, idNew, z3GRBVarMap);
        }
        return model;
    }

    public GRBModel addAConstrGRB(BoolExpr be, GRBModel model, String id, HashMap<IntExpr, GRBVar> z3GRBVarMap) {//be is an arith constraint
        if (!be.isTrue()) {
            GRBLinExpr one = new GRBLinExpr();
            one.addConstant(1);
            GRBLinExpr zero = new GRBLinExpr();
            one.addConstant(0);

            try {
                if (be.isFalse()) { //adding 0=<1
                    //System.out.println("here === ");
                    model.addConstr(one, GRB.LESS_EQUAL, zero, id);
                    return model;
                }
                Expr[] exprs = be.getArgs();

                //System.out.println("l r " + exprs[0] + " " + exprs[1]);
                GRBLinExpr grbExpr0 = z3Expr2GRBExpr((ArithExpr) exprs[0], model, z3GRBVarMap);
                GRBLinExpr grbExpr1 = z3Expr2GRBExpr((ArithExpr) exprs[1], model, z3GRBVarMap);
                //  System.out.println("l r "+exprs[0] +" "+exprs[1] );
                if (be.isGE()) {
                    model.addConstr(grbExpr0, GRB.GREATER_EQUAL, grbExpr1, id);
                    //System.out.println(" constr ============= "+ GurobiInterface.constrString(grbExpr0, ">=", grbExpr1));
                } else if (be.isLE()) {
//                    System.out.println(" constr ============= " + GurobiInterface.constrString(grbExpr0, "<=", grbExpr1));
                    model.addConstr(grbExpr0, GRB.LESS_EQUAL, grbExpr1, id);

                } else if (be.isEq()) {
                    model.addConstr(grbExpr0, GRB.EQUAL, grbExpr1, id);
                    //System.out.println(" constr ============= "+ GurobiInterface.constrString(grbExpr0, "=", grbExpr1));
                } else {
                    System.out.println("exceptional case");
                }
            } catch (GRBException ex) {
                System.out.println("Error code: " + ex.getErrorCode() + ". "
                        + ex.getMessage());

            } catch (Exception e) {
                e.printStackTrace();
            }

        }
        return model;
    }

    public static GRBLinExpr z3Expr2GRBExpr(ArithExpr e, GRBModel model, HashMap<IntExpr, GRBVar> z3GRBVarMap) {
        GRBLinExpr grbExpr = new GRBLinExpr();
        try {
            if (e.isIntNum()) {//constant
                grbExpr.addConstant(Double.parseDouble(e.toString()));
                //return grbExpr;
            } else if (e.isConst() && e.isInt()) {
                grbExpr.addTerm(1, z3GRBVarMap.get(e));
            } //   return grbExpr;
            else { //e should be some arithmetic operator
                if (e.isAdd()) {
                    Expr[] exprs = e.getArgs();
                    for (int i = 0; i < exprs.length; i++) {
                        grbExpr.add(z3Expr2GRBExpr((ArithExpr) exprs[i], model, z3GRBVarMap));
                    }
                } else if (e.isSub()) {
                    Expr[] exprs = e.getArgs();
                    GRBLinExpr grbExprM;
                    for (int i = 0; i < exprs.length; i++) {
                        if (i == 0) {
                            grbExprM = z3Expr2GRBExpr((ArithExpr) exprs[i], model, z3GRBVarMap);
                            grbExpr.add(grbExprM);
                        } else {
                            grbExprM = z3Expr2GRBExpr((ArithExpr) exprs[i], model, z3GRBVarMap);
                            grbExpr.multAdd(-1, grbExprM);
                        }
                    }
                    //return grbExpr;
                } else if (e.isMul()) {//assume the first one to be a coefficient
                    Expr[] exprs = e.getArgs();
                    Double coeff;
                    boolean const0 = isConstant(exprs[0]);
                    if (const0) {

                        if (exprs[0].isUMinus()) {
                            coeff = -Double.parseDouble(exprs[0].getArgs()[0].toString());
                        } else {
                            coeff = Double.parseDouble(exprs[0].toString());
                        }
                        GRBLinExpr grbExprMul = z3Expr2GRBExpr((ArithExpr) exprs[1], model, z3GRBVarMap);
                        grbExpr.multAdd(coeff, grbExprMul);
                    } else {
                        boolean const1 = isConstant(exprs[1]);
                        if (const1) {
                            if (exprs[1].isUMinus()) {
                                coeff = -Double.parseDouble(exprs[1].getArgs()[0].toString());
                            } else {
                                coeff = Double.parseDouble(exprs[1].toString());
                            }
                            GRBLinExpr grbExprMul = z3Expr2GRBExpr((ArithExpr) exprs[0], model, z3GRBVarMap);
                            grbExpr.multAdd(coeff, grbExprMul);
                        }
                    }
                    //return grbExpr;
                }
            }
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return grbExpr;
    }

//e=X*c or c*X
    public static boolean isConstant(Expr e) {
        if (e.isUMinus()) {
            return e.getArgs()[0].isIntNum();
        } else {
            return e.isIntNum();
        }
    }

    public static BoolExpr simplifyArithNeg(BoolExpr be, Context ctx) {
        Expr[] exprs = be.getArgs();
        ArithExpr a0 = (ArithExpr) exprs[0];
        ArithExpr a1 = (ArithExpr) exprs[1];
        if (be.isLE()) {
            return ctx.mkGt(a0, a1);
        }
        if (be.isLT()) {
            return ctx.mkGe(a0, a1);
        }
        if (be.isGE()) {
            return ctx.mkLt(a0, a1);
        }
        if (be.isGT()) {
            return ctx.mkLe(a0, a1);
        }
        //otherwise is =
        return ctx.mkOr(ctx.mkGt(a0, a1), ctx.mkLt(a0, a1));
    }

    public static BoolExpr listToBF(Context ctx, BoolExpr[] liaFormulas) {
        BoolExpr acc = ctx.mkTrue();
        if (liaFormulas.length > 0) {
            acc = liaFormulas[0];
        }
        for (int i = 1; i < liaFormulas.length; i++) {
            acc = ctx.mkAnd(acc, liaFormulas[i]);
        }
        return acc;
    }

    public static void print(int i, String s) {
        if (i != 0) {
            System.out.println(s);
        }
    }

    public long z3IntExpr2Long(IntNum e) {
        try {
            return Long.parseLong(e.toString());
        } catch (NumberFormatException ex) {
            ex.printStackTrace();
        }
        return Integer.MAX_VALUE;
    }

    public static Symbol[] reverseArray(Symbol[] varNames) {
        List<Symbol> varList = Arrays.asList(varNames);
        Collections.reverse(varList);
        return varList.toArray(new Symbol[varList.size()]);
    }

}
