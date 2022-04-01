package edu.melbourne.MAsat;

/*
 all constraints  are transformed with delta to linear arithmetic lazily
 */
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BitVecExpr;
import com.microsoft.z3.BitVecSort;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.IntNum;
import com.microsoft.z3.IntSort;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.Model;
import com.microsoft.z3.Quantifier;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Sort;
import com.microsoft.z3.Status;
import com.microsoft.z3.Symbol;
import com.microsoft.z3.Z3Exception;
import gurobi.GRB;
import gurobi.GRBConstr;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import gurobi.GRBVar;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Set;

/**
 *
 * @author kafle
 */
public class InterpolantBendersDecompWFixedSizeLazyPP {

    //orders the keysets; the order is the same as the insertion order
    LinkedHashMap<String, TransformedFormula> transformedFormulasA;
    LinkedHashMap<String, TransformedFormula> transformedFormulasB;
    HashMap<IntExpr, GRBVar> z3GRBVarMap;
    HashMap<IntExpr, Integer> sizeIntVar;
    int counter; //counts the number of delta introduced
    int refinementCount;
    int disjointRefinementCount;
    int nrConstraintRelaxed;
    boolean deltaGenerated;
    IntExpr lastDelta;
    HashSet<IntExpr> boundedVars;
    HashSet<BvVariable> vars;
    GRBVar[] grbVars;
    int formulaCount;
    IntExpr[] deltas;
    boolean deltaValuesModified;
    HashMap<String, BoolExpr> idStringToBoolExpr;
    String[] currentAssumptionsA;
    String[] previousAssumptionsA;
    String[] currentAssumptionsB;
    String[] previousAssumptionsB;
    BoolExpr cutAssumptionsA;
    BoolExpr cutAssumptionsB;
    static final int PRINT_FLAG = 0; //0=do not print, any other number print
    static final int COEFF_THRESHOLD = 500;
    String resultLogic = "QF_LIA"; //specifies whether the result is QF_BV or QF_LIA

    public void initialize() {
        counter = 1;
        transformedFormulasA = new LinkedHashMap<>();
        transformedFormulasB = new LinkedHashMap<>();
        refinementCount = 0;
        disjointRefinementCount = 0;
        nrConstraintRelaxed = 0;
        deltaGenerated = false; //no delta expr has been generated
        boundedVars = new HashSet<>();
        vars = new HashSet<>();
        formulaCount = 0;
        deltaValuesModified = false;
        idStringToBoolExpr = new HashMap<>();
        z3GRBVarMap = new HashMap<>();
        sizeIntVar = new HashMap<>();
    }

    public void dispose() {
        transformedFormulasA = null;
        boundedVars = null;
        vars = null;
        z3GRBVarMap = null;
        grbVars = null;
        deltas = null;
        idStringToBoolExpr = null;
        sizeIntVar = null;
    }

    public Witness solveArithFormula(GRBModel grbModel, Context ctx, Z3Interface z3Interface, GurobiInterface grbInterface) {
        grbInterface.resetModel(grbModel);
//        Util.print(PRINT_FLAG, "calling gurobi");
        int status = grbInterface.optimize(grbModel);
//        Util.print(PRINT_FLAG, "gurobi returned");

        if (status == GRB.Status.INFEASIBLE) {
//            Util.print(PRINT_FLAG, "querying unsat core");
            String[] unsatCore = grbInterface.getUnsatCore(grbModel); // = currentAssumptions;
//            Util.print(PRINT_FLAG, "unsat core returned");
//            Util.print(PRINT_FLAG, "unsat core:  " + Message.printUnsatCore(unsatCore));
//            printCoreConstrants(unsatCore, ctx);
            return new Witness(false, null, unsatCore);
        } else if (status == GRB.Status.OPTIMAL) {
            return new Witness(true, grbModel, null);
        } else {
            System.out.println("solver returned unknown status..................");
            return null; // solver error
        }
    }

    /**
     * changes grbModel to Z3Model returns null if any of the var takes
     * non-integer solution
     */
    public Model getZ3ModelFrom(GRBModel grbModel, Context ctx) {
        Model z3Model;
        Solver z3Solver = ctx.mkSolver();
        GRBVar[] grbVars = grbModel.getVars();
        String varName;
        long varValue;
        IntExpr z3Var;
        IntNum z3Value;
        for (GRBVar v : grbVars) {
            try {
                varName = v.get(GRB.StringAttr.VarName);
                double d = v.get(GRB.DoubleAttr.X);
//                System.out.println("var value "+varName+" "+d);
                varValue = (long) d;
                if (d % 1 != 0) { //this means it is not an integer solution
                    return null;
                }
                z3Var = ctx.mkIntConst(varName);
                z3Value = ctx.mkInt(varValue);
                z3Solver.add(ctx.mkEq(z3Var, z3Value));
            } catch (GRBException ex) {
                ex.printStackTrace();
            }
        }
        z3Solver.check();
        z3Model = z3Solver.getModel(); //definitely gonna have a model
        return z3Model;
    }

    /**
     * checking whether a Z-model is a Z_m model using Gurobi
     */
    public Witness maModelWModuloGRB(GRBModel grbModel, Context ctx, GurobiInterface grbInterface) {
        //getZ3ModelFrom( grbModel,  ctx);
        BoolExpr maExpr = null;
        TransformedFormula tf;
        String arithOperator = "";
        GRBLinExpr grbE1 = null, grbE2 = null;
        ArrayList<String> conflictConstr = new ArrayList<>();
        for (String key : transformedFormulasA.keySet()) {
            tf = transformedFormulasA.get(key);
            if (tf.getStatus() == 0) { //transformed are already evaluated under modulo
                maExpr = tf.getOriginalFormula();
                //only enough to check non-relaxed formulas, since all other will be satisfied
                Expr[] exprs = maExpr.getArgs();
                if (maExpr.isGE()) {
                    arithOperator = ">=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0].simplify(), grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1].simplify(), grbModel, z3GRBVarMap);

                } else if (maExpr.isLE()) {
                    arithOperator = "<=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0].simplify(), grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1].simplify(), grbModel, z3GRBVarMap);

                } else if (maExpr.isEq()) {
                    arithOperator = "=";
                    grbE1 = Util.z3Expr2GRBExpr((ArithExpr) exprs[0].simplify(), grbModel, z3GRBVarMap);
                    grbE2 = Util.z3Expr2GRBExpr((ArithExpr) exprs[1].simplify(), grbModel, z3GRBVarMap);

                }
                Boolean evalRes = grbInterface.evalConstraintInModel(grbE1, arithOperator, grbE2);
                //System.out.println("eval expr "+s);
                if (evalRes == Boolean.FALSE) {
                    conflictConstr.add(key);
                    //System.out.println("============-====================check failed for clause " + key);
                }
            }
        }
        int size = conflictConstr.size();
        if (size == 0) {
//            System.out.println("=================== ma_sat =========== ");
            return new Witness(true, grbModel, null);
        } else {
            return new Witness(false, null, conflictConstr.toArray(new String[size]));
        }
    }

    public IntExpr nextDelta(Context ctx, int counter) {
        String s = "delta_" + Integer.toString(counter);
        IntExpr deltaExpr = (IntExpr) ctx.mkIntConst(s);
        lastDelta = deltaExpr;
        return deltaExpr;
    }

    public ArithExpr genDeltaExpr(int exprWidth, Context ctx, String key) {
        IntExpr ie = nextDelta(ctx, counter);
        counter++;
        ArithExpr deltaExpr = ctx.mkMul(ctx.mkInt(Util.modulo_m(exprWidth)), ie);
        return deltaExpr;
    }

    public BoolExpr genVarsBounds(Context ctx, HashSet<BvVariable> vars, HashSet<BvVariable> alreadyBoundedVars) {
        BoolExpr acc = ctx.mkTrue();
        BvVariable ie;
        Iterator<BvVariable> itr = vars.iterator();
        if (itr.hasNext()) {
            ie = itr.next();
            if (!alreadyBoundedVars.contains(ie)) {
                alreadyBoundedVars.add(ie);
                acc = genVarBounds(ctx, ie);
            }
        }
        while (itr.hasNext()) {
            ie = itr.next();
            if (!alreadyBoundedVars.contains(ie)) {
                alreadyBoundedVars.add(ie);
                acc = ctx.mkAnd(acc, genVarBounds(ctx, ie));
            }
            //acc = ctx.mkAnd(acc, genVarBounds(ctx, ie));
        }
        return acc;
    }

    public BoolExpr genVarBounds(Context ctx, BvVariable var) {
        BoolExpr loBoundvar, upBoundvar;
        IntExpr ie = ctx.mkIntConst(var.getName());
        int varSortSize = var.getSortSize();
        loBoundvar = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg(varSortSize)), ie);
        upBoundvar = ctx.mkLe(ie, (ArithExpr) ctx.mkInt(Util.max_pos(varSortSize)));
        return ctx.mkAnd(loBoundvar, upBoundvar);
    }

    /**
     * when both bounds coincide
     */
    public BoolExpr genDeltaBound(Context ctx, IntExpr delta, IntExpr bound) {
        return ctx.mkEq(delta, bound);
    }

    public BoolExpr genExprBounds(Context ctx, ArithExpr e1, ArithExpr e2) {
        try {
            BoolExpr loBoundExpr1, upBoundExpr1, loBoundExpr2, upBoundExpr2, loUpBoundExpr1, loUpBoundExpr2;
            BoolExpr beTrue = ctx.mkTrue();
            // System.out.println("e1 and e2 "+e1 + " "+e2);
            if (e1.isIntNum() || (e1.isApp() && e1.getNumArgs() == 0 && e1.isInt())) { //var bounds are generated at the end
                loUpBoundExpr1 = beTrue;
            } else {
                loBoundExpr1 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), e1);
                upBoundExpr1 = ctx.mkLe(e1, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr1 = ctx.mkAnd(loBoundExpr1, upBoundExpr1);
            }
            if (e2.isIntNum() || (e2.isApp() && e2.getNumArgs() == 0 && e2.isInt())) {
                loUpBoundExpr2 = beTrue;
            } else {
                loBoundExpr2 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), e2);
                upBoundExpr2 = ctx.mkLe(e2, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr2 = ctx.mkAnd(loBoundExpr2, upBoundExpr2);
            }
            return ctx.mkAnd(loUpBoundExpr1, loUpBoundExpr2);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genLoBound(Context ctx, ArithExpr arithExpr, int exprWidth) {
        try {
            BoolExpr res = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg(exprWidth)), arithExpr);
            return Z3Interface.standariseArithInEq(res, ctx);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genUpBound(Context ctx, ArithExpr arithExpr, int exprWidth) {
        try {
            BoolExpr res = ctx.mkLe(arithExpr, (ArithExpr) ctx.mkInt(Util.max_pos(exprWidth)));
            return Z3Interface.standariseArithInEq(res, ctx);
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    public BoolExpr genBounds(Context ctx, ArithExpr arithExpr) {
        try {
            BoolExpr loBoundExpr1, upBoundExpr1, loUpBoundExpr1;
            BoolExpr beTrue = ctx.mkTrue();
            // System.out.println("e1 and e2 "+e1 + " "+e2);
            if (arithExpr.isConst() && arithExpr.isInt()) { //var bounds are generated at the end
                loUpBoundExpr1 = beTrue;
            } else {
                loBoundExpr1 = ctx.mkLe((ArithExpr) ctx.mkInt(Util.min_neg()), arithExpr);
                upBoundExpr1 = ctx.mkLe(arithExpr, (ArithExpr) ctx.mkInt(Util.max_pos()));
                loUpBoundExpr1 = ctx.mkAnd(loBoundExpr1, upBoundExpr1);
            }
            return loUpBoundExpr1;
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    /**
     * Graeme's bound
     */
    public BoolExpr genOptDeltaBound(String id, Context ctx, BitVecExpr e, IntExpr delta, GurobiInterface grbInterface, GRBEnv env, GRBModel grbModel, Solver deltaSolver, PreProcessBV ppbv) {
        long min, max;
        long minDelta, maxDelta;
        GRBVar grbDeltaVar;
        HashSet<BvVariable> vars = Util.collectBvVars(e, ctx);
        max = maxExpr(grbInterface, env, ctx, e, ppbv);
        min = minExpr(grbInterface, env, ctx, e, ppbv);
        minDelta = min / Util.modulo_m() - 1; // "/" is an integer division
        maxDelta = max / Util.modulo_m() + 1;
        //System.out.println("min max==================================== " + delta + "  " + minDelta + " " + maxDelta);
        //creating delta var as a gurobi var
        grbDeltaVar = Util.createGRBVar(grbModel, delta, minDelta, maxDelta);
        z3GRBVarMap.put(delta, grbDeltaVar);
        grbInterface.updateModel(grbModel);
        BoolExpr deltaBounds = genDeltaBounds(ctx, delta, ctx.mkInt(minDelta), ctx.mkInt(maxDelta));
        deltaSolver.add(ctx.mkImplies(idStringToBoolExpr.get(id), deltaBounds));
        return deltaBounds;
    }

    public BoolExpr genDeltaBounds(Context ctx, IntExpr delta, IntExpr loBound, IntExpr upBound) {
        BoolExpr loBoundDelta, upBoundDelta;
        loBoundDelta = ctx.mkLe(loBound, delta);
        upBoundDelta = ctx.mkLe(delta, upBound);
        return ctx.mkAnd(loBoundDelta, upBoundDelta);
    }

    public long maxExpr(GurobiInterface grbInterface, GRBEnv env, Context ctx, BitVecExpr e, PreProcessBV ppbv) {
        GRBModel grbMaxOpt = grbInterface.getGRBModel(env);
        HashSet<BvVariable> z3VarsExpr = Util.collectBvVars(e, ctx);
        HashMap<IntExpr, GRBVar> z3GRBVarMapLocal = new HashMap<>();
        Util.createZ3GRBVarMap(grbMaxOpt, z3VarsExpr, z3GRBVarMapLocal, ctx);
        grbInterface.updateModel(grbMaxOpt);
        BoolExpr constraints = genVarsBounds(ctx, z3VarsExpr, new HashSet<>());
        grbMaxOpt = new Util().addConstrsGRB(constraints, grbMaxOpt, "dBMax", z3GRBVarMapLocal);
        GRBLinExpr expr = Util.z3Expr2GRBExpr(ppbv.convertToLIAExpr(e, ctx), grbMaxOpt, z3GRBVarMapLocal);
        grbInterface.GRBSetMaximize(expr, grbMaxOpt);
        grbInterface.optimize(grbMaxOpt);
        long max = (long) grbInterface.getOptValue(grbMaxOpt);
        grbMaxOpt = null;
        return max;
    }

    public long minExpr(GurobiInterface grbInterface, GRBEnv env, Context ctx, BitVecExpr e, PreProcessBV ppbv) {
        GRBModel grbMinOpt = grbInterface.getGRBModel(env);
        HashSet<BvVariable> z3VarsExpr = Util.collectBvVars(e, ctx);
        HashMap<IntExpr, GRBVar> z3GRBVarMapLocal = new HashMap<>();
        Util.createZ3GRBVarMap(grbMinOpt, z3VarsExpr, z3GRBVarMapLocal, ctx);
        grbInterface.updateModel(grbMinOpt);
        BoolExpr constraints = genVarsBounds(ctx, z3VarsExpr, new HashSet<>());
        grbMinOpt = new Util().addConstrsGRB(constraints, grbMinOpt, "dBMin", z3GRBVarMapLocal);
        GRBLinExpr expr = Util.z3Expr2GRBExpr(ppbv.convertToLIAExpr(e, ctx), grbMinOpt, z3GRBVarMapLocal);
        grbInterface.GRBSetMinimize(expr, grbMinOpt);
        grbInterface.optimize(grbMinOpt);
        long min = (long) grbInterface.getOptValue(grbMinOpt);
        grbMinOpt = null;
        return min;
    }

    public ArithExpr genAExprBVNumber(int exprWidth, Context ctx, IntNum e) {
        IntExpr eInt = ctx.mkInt(Util.getModuloM((IntNum) e, exprWidth)); //brings everything under modulo (16 mod 5= 1)
        long num = Long.parseLong(eInt.toString());
        if (num < 0) { //if is a neg nr, return M+e
            num = Util.modulo_m(exprWidth) + num;
            return (ArithExpr) ctx.mkInt(num);
        }
        return eInt;
    }

    public ArithExpr genAExprFromBvExpr(int exprWidth, Context ctx, String key, ArithExpr e, GRBModel grbModel, GurobiInterface grbInterface) {//number must have a fixed interpretation
        if (e.isIntNum()) { //z3 treats (- 8) as unary minus not as integer but -8 (without space) is integer in z3 
            return genAExprBVNumber(exprWidth, ctx, (IntNum) e);
        }
        if (e.isConst() && e.isInt()) {
            return e;
        }
        ArithExpr deltaExpr = genDeltaExpr(exprWidth, ctx, key);
        ArithExpr ae = ctx.mkAdd(e, deltaExpr);
        deltaGenerated = true; //to track if the delta expr was generated
        return ae;
    }

    public boolean isArithInEq(Expr e) {
        return (e.isLE() || e.isGE() || e.isGT() || e.isLT() || e.isEq());
    }

    public boolean isBVOperation(Expr beBV) {
        return (beBV.isEq() || beBV.isBVULE() || beBV.isBVULT() || beBV.isBVUGT() || beBV.isBVUGE());
    }

    /**
     * translates bv-expr to equivalent arithmetic-exprs
     */
//    public BoolExpr genEquivalentAInEqFromBvInEq(Context ctx, String key, Expr e, boolean negate, Z3Interface z3Interface, GRBModel gRBModel, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver, PreProcessBV preProcessBV) {
//        System.out.println("expr is "+e);
//        Expr[] andExprs, orExprs;
//        BoolExpr beOr = ctx.mkFalse(), beAnd = ctx.mkTrue();
//        if (e.isFalse() || e.isTrue()) {
//            return (BoolExpr) e;
//        }
//        if (e.isNot()) { //pre-processing has already gotten rid of this
//            return ctx.mkNot(genEquivalentAInEqFromBvInEq(ctx, key, e.getArgs()[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV));
//        }
//
//        if (e.isOr()) {
//            orExprs = e.getArgs();
//            if (orExprs.length > 0) {
//                beOr = genEquivalentAInEqFromBvInEq(ctx, key, orExprs[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV);
//            }
//            for (int i = 1; i < orExprs.length; i++) {
//                beOr = ctx.mkOr(beOr, genEquivalentAInEqFromBvInEq(ctx, key, orExprs[i], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV));
//            }
//            return beOr;
//        }
//
//        if (e.isAnd()) {
//            andExprs = e.getArgs();
//            if (andExprs.length > 0) {
//                beAnd = genEquivalentAInEqFromBvInEq(ctx, key, andExprs[0], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV);
//            }
//            for (int i = 1; i < andExprs.length; i++) {
//                beAnd = ctx.mkOr(beAnd, genEquivalentAInEqFromBvInEq(ctx, key, andExprs[i], negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV));
//            }
//            return beAnd;
//        }
//        if (isBVOperation(e)) {
////            System.out.println("e " + e);
//            return genAinEqFromAtomicBvinEq(ctx, key, e, negate, z3Interface, gRBModel, grbInterface, env, deltaSolver, preProcessBV);
//        }
//        if (e.isConst() || e.isBV()) { //boolean variable of bit-vector sort
//            //returned as it as integer constant
//            return ctx.mkBoolConst(e.toString());
//        }
//        return null;
//    }
    //input is arith inequalities (not equalities)
    public BoolExpr genAinEqFromAtomicBvinEq(Context ctx, String key, Expr e, Z3Interface z3Interface, GRBModel gRBModel, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver, PreProcessBV preProcessBV) {
        ArithExpr ae1 = null, ae2 = null;
        deltas = new IntExpr[2];
        BoolExpr be = null;
        Expr[] exprs = e.getArgs();
        ArithExpr aExpr1 = (ArithExpr) preProcessBV.convertToLIAExpr((BitVecExpr) exprs[0], ctx).simplify();
//        System.out.println("non simp "+aExpr1);
//         System.out.println(" simp "+aExpr1.simplify());
        ae1 = genAExprFromBvExpr(((BitVecExpr) exprs[0]).getSortSize(), ctx, key, aExpr1, gRBModel, grbInterface);
        if (deltaGenerated) {
            IntExpr delta1 = lastDelta;
            deltas[0] = delta1;
            deltaGenerated = false;
        }
        ArithExpr aExpr2 = (ArithExpr) preProcessBV.convertToLIAExpr((BitVecExpr) exprs[1], ctx).simplify();
        ae2 = genAExprFromBvExpr(((BitVecExpr) exprs[1]).getSortSize(), ctx, key, aExpr2, gRBModel, grbInterface);
        if (deltaGenerated) {
            IntExpr delta2 = lastDelta;
            deltas[1] = delta2;
            deltaGenerated = false;
        }
        if (e.isEq()) {
            be = ctx.mkEq(ae1, ae2);
        } else if (e.isBVUGT()) {
            be = ctx.mkGt(ae1, ae2);

        } else if (e.isBVUGE()) {
            be = ctx.mkGe(ae1, ae2);

        } else if (e.isBVULT()) {
            be = ctx.mkLt(ae1, ae2);

        } else if (e.isBVULE()) {
            be = ctx.mkLe(ae1, ae2);

        } else {
            System.out.println(e + "is not an arithmetic inequality ");
        }
        return be;
    }

    /**
     * (a+b.c-c.d)mod m = a mod m + b.c mod m - c.d mod m. But if this result is
     * negative, which is equivalent to m-result
     */
//    public ArithExpr genModuloAExpr(Context ctx, ArithExpr e) {//number must have a fixed interpretation
//        IntExpr moduloM = ctx.mkInt(Util.modulo_m());
//        IntExpr lowerBound = ctx.mkInt(Util.min_neg());
//        IntExpr ae = ctx.mkMod((IntExpr) e, moduloM);
//        return (ArithExpr) ctx.mkITE(ctx.mkLt(ae, lowerBound), ctx.mkAdd(moduloM, ae), ae);
//    }
    public String getIneqSign(String id) {
        BoolExpr formula = transformedFormulasA.get(id).getOriginalFormula();
        if (formula.isGE()) {
            return ">=";
        }
        if (formula.isLE()) {
            return "<=";
        }
        return "=";
    }

    public String getIneqSign(BoolExpr formula) {
        if (formula.isGE()) {
            return ">=";
        }
        if (formula.isLE()) {
            return "<=";
        }
        return "=";
    }

    public ArithExpr getDeltaExprCut(IntExpr delta1, IntExpr delta2, String exprSign, Context ctx) {
        if (exprSign.equals(">=")) {
            return ctx.mkSub(delta1, delta2);
        }
        if (exprSign.equals("<=")) {
            return ctx.mkSub(delta2, delta1);
        }
        //equal case
        return ctx.mkSub(delta1, delta2);
    }

    //linear cut but maybe unsound, myway
    public void addLinearCutUnsatCore(Context context, String[] conflicts, Solver deltaSolver, Model previousDeltaModel) {
        BoolExpr cutExpr = context.mkFalse();
        String id;
        int index;
        TransformedFormula tf;
        IntExpr zero = context.mkInt(0);
        ArithExpr acc = context.mkInt(0);
        for (String coreId : conflicts) {
            id = mapIdToOriginal(context, coreId);
            tf = transformedFormulasA.get(id);
            index = getConstraintIndex(coreId);
            ArithFormula af = tf.getFormula().get(index);
            acc = context.mkAdd(acc, context.mkSub(af.getDeltaExpr(), (ArithExpr) Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr())));
        }
        cutExpr = context.mkGt(acc, zero);
        cutExpr = (BoolExpr) cutExpr.simplify();
//        System.out.println("cut is ==================" + cutExpr);
        deltaSolver.add(cutExpr);
    }

    /*
     Graeme's way
     */
    public void addCutUnsatCoreGraeme(HashMap<String, TransformedFormula> transformedFormulas, Context context, String[] conflicts, Solver deltaSolver, Model previousDeltaModel) {
        BoolExpr cutExpr = context.mkFalse();
        String id;
        int index;
        BoolExpr cutSingleConstr;
        TransformedFormula tf;
        BoolExpr boolId;
        BoolExpr coreAssumption = context.mkTrue();
        //IntExpr zero = context.mkInt(0);
        for (String coreId : conflicts) {
            id = mapIdToOriginal(context, coreId);
            boolId = getIdsBoolExpr(id, context);
            coreAssumption = context.mkAnd(coreAssumption, boolId);
            tf = transformedFormulas.get(id);
            if (tf.isPrecise() || !tf.isDeltaIntroduced()) {
                cutSingleConstr = context.mkNot(idStringToBoolExpr.get(id));
                cutExpr = context.mkOr(cutExpr, cutSingleConstr);
            } else {
                index = getConstraintIndex(coreId);
                ArithFormula af = tf.getFormula().get(index);
                //System.out.println("core generating "+coreId+" "+af.getFormula());
                if (af.isEquality()) {
                    cutSingleConstr = context.mkNot(context.mkEq(af.getDeltaExpr(), Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr())));
                    //cutSingleConstr = context.mkImplies(cutAssumptions, cutSingleConstr);
                    cutExpr = context.mkOr(cutExpr, cutSingleConstr);

                } else {
                    cutSingleConstr = context.mkGt(af.getDeltaExpr(), (ArithExpr) Z3Interface.evalExprInModel(previousDeltaModel, af.getDeltaExpr()));
                    //cutSingleConstr = context.mkImplies(cutAssumptions, cutSingleConstr);
                    //System.out.println("cut is ==================" + cutSingleConstr);
                    cutExpr = context.mkOr(cutExpr, cutSingleConstr);
                }
                //System.out.println("cut before single ==================" + cutSingleConstr);
            }
        }
        cutExpr = context.mkImplies(coreAssumption, cutExpr);
//        System.out.println("cut before ==================" + cutExpr);
        cutExpr = (BoolExpr) cutExpr.simplify();
//        System.out.println("cut is ==================" + cutExpr);
        deltaSolver.add(cutExpr);
    }

    public boolean isIdInAssumption(String id, BoolExpr[] assumptions) {
        for (int i = 0; i < assumptions.length; i++) {
            if (id.equals(assumptions[i].toString())) {
                return true;
            }
        }
        return false;
    }
//returns assumptions in (previous-current)

    public ArrayList<String> diffAssumptions(String[] previous, String[] current) {
        ArrayList<String> diffAssumptions = new ArrayList<>();
        HashSet<String> currentSet = new HashSet<String>(Arrays.asList(current));
        if (previous != null) {
            for (String s : previous) {
                if (!currentSet.contains(s)) {
                    diffAssumptions.add(s);
                }
            }
        }
        return diffAssumptions;
    }

    public void removeConstraintAlreadyInGrbSolver(GurobiInterface grbInterface, GRBModel grbModel, int refinementCount, String[] previousAssumptions, String[] currentAssumptions) {
        TransformedFormula tf1;
        if (refinementCount > 0) { //before that no constraint has been added
            ArrayList<String> diffAssumptions = diffAssumptions(previousAssumptions, currentAssumptions);
            //remove constraints pertaining to the previous assumptions
            for (String s : diffAssumptions) {
                //remove constraints
                tf1 = transformedFormulasA.get(s);
                int nrConstraints = tf1.getFormulaSize();
                boolean alreadyInSolver = tf1.isAlreadyInTransformedFormInThesolver();
                if (alreadyInSolver) { //delta model will  change and the constraint cannot stay in the solver
                    for (int i = 0; i < nrConstraints; i++) {
                        String idNew = s + "__r__" + i;
                        grbInterface.removeConstraint(grbModel, idNew);
                    }
                }
                tf1.setAlreadyInTransformedFormInThesolver(false);
            }
        }
    }

    public BoolExpr computeInterpolantTransformedFormula(Z3Interface z3Interface, InterpolationContext context, GRBEnv env, GurobiInterface grbInterface, Solver solverA, Solver solverB, GRBModel grbModelA, GRBModel grbModelB) {
        BoolExpr interpolant = context.mkFalse(); //final interpolant formula
        Model modelA;
        while (z3Interface.checkFormula(solverA) == Status.SATISFIABLE) { //external loop, corresponding to formula A
            modelA = solverA.getModel();
            System.out.println("outside ");
            previousAssumptionsA = currentAssumptionsA;
            currentAssumptionsA = getCurrentAssumptionUnder(transformedFormulasA, modelA, context, true);
            if (currentAssumptionsA.length == 0) {
                System.out.println("================================all assumptions are false==================================");
                return interpolant;
//            return null; //all delta coeff are tried, and find a different disjunct, 
            }
            //the following notMuA is to use later, so that we do not need to recompute within the inner loop
            BoolExpr notMuA = blockPreviousModel(transformedFormulasA, context, solverA, modelA, currentAssumptionsA, cutAssumptionsA);
            //removeConstraintAlreadyInGrbSolver(grbInterface, grbModelA, refinementCount, previousAssumptionsA, currentAssumptionsA);

            BoolExpr formulaUnderCurrentAssA = addConstraintsToGurobiAndReturnAddedFormulas(transformedFormulasA, currentAssumptionsA, env, grbInterface, grbModelA, context, z3Interface, modelA);

            Witness LIAWitnessA = solveArithFormula(grbModelA, context, z3Interface, grbInterface);
            if (!LIAWitnessA.isSatisfiable()) {
                updateModelWithCutFromCore(transformedFormulasA, LIAWitnessA, context, solverA, modelA);
                refinementCount++;
                System.out.println("here ");
            } else {
                //partial interpolant of a_i with B
                BoolExpr interpolantConj = context.mkTrue();
                Solver solverbInnerLoop = z3Interface.getSolverClone(solverB, context);
//                System.out.println("beginning");
//                printAssertion(solverB);
                while (z3Interface.checkFormula(solverbInnerLoop) == Status.SATISFIABLE) { //external loop, corresponding to formula A
                    Model modelB = solverbInnerLoop.getModel();
                    System.out.println("inner loop");
//                    System.out.println("model b " + modelB);
                    previousAssumptionsB = currentAssumptionsB;
                    currentAssumptionsB = getCurrentAssumptionUnder(transformedFormulasB, modelB, context, false);
//                    if (currentAssumptionsB.length == 0) {
//                        System.out.println("================================all assumptions are false==================================");
//                        return interpolant;
//                    }
//                    System.out.println("current assumption");
//                    printAssumption(currentAssumptionsB);
                    removeConstraintAlreadyInGrbSolver(grbInterface, grbModelB, refinementCount, previousAssumptionsB, currentAssumptionsB);

                    BoolExpr formulaUnderCurrentAssB = addConstraintsToGurobiAndReturnAddedFormulas(transformedFormulasB, currentAssumptionsB, env, grbInterface, grbModelB, context, z3Interface, modelB);
//                    System.out.println("B formula " + formulaUnderCurrentAssB);
                    Witness LIAWitnessB = solveArithFormula(grbModelB, context, z3Interface, grbInterface);
                    if (!LIAWitnessB.isSatisfiable()) {
                        updateModelWithCutFromCore(transformedFormulasB, LIAWitnessB, context, solverbInnerLoop, modelB);
                        //System.out.println("core ");
                        //printAssertion(solverB);
                        //even for solver A, use the modelB: eliminate that quotient values from sover A
                        addCutUnsatCoreGraeme(transformedFormulasB, context, LIAWitnessB.getUnsatCore(), solverB, modelB);
                        //refinementCount++;
                    } else {
                        BoolExpr partialInterpolant = getInterpolant(formulaUnderCurrentAssA, formulaUnderCurrentAssB, context, z3Interface);
                        System.out.println("partial " + partialInterpolant);
                        if (partialInterpolant == null) {
                            System.err.println("The constraints are satisfiable: so no interpolant.");
                            System.exit(1);
                        }
                        interpolantConj = context.mkAnd(interpolantConj, partialInterpolant);
                        BoolExpr notMuB = blockPreviousModel(transformedFormulasB, context, solverbInnerLoop, modelB, currentAssumptionsB, cutAssumptionsB);
                        solverbInnerLoop.add(notMuB); // not the current mu_b
                        System.out.println("blocking =====");
                        //printAssertion(solverB);
                        //solverA.add(context.mkOr(notMuA, notMuB)); // not the conjunction mu_a and mu_b 
                        //refinementCount++;
                    }
                }
                //since interpolantConj is disjoined with interpolant, we cannot get more general than this
                if (interpolantConj.isTrue()) {
                    return context.mkTrue();
                }
                interpolant = context.mkOr(interpolant, interpolantConj);
                solverA.add(notMuA);
                refinementCount++;
            }
        }
        return interpolant;
    }

    public BoolExpr getInterpolant(BoolExpr formulaA, BoolExpr formulaB, InterpolationContext context, Z3Interface z3Interface) {
        try {
            //System.out.println("formula a before " + formulaA);
            //System.out.println("formula b before" + formulaB);
            formulaA = getFormulaWVarBounds(formulaA, context, z3Interface);
            //System.out.println("formula a " + formulaA);
            formulaB = getFormulaWVarBounds(formulaB, context, z3Interface);
            //System.out.println("formula b " + formulaB);
            return z3Interface.computeInterpolant(formulaA, formulaB, context);
        } catch (Z3Exception z3e) {
            z3e.printStackTrace();
        }
        return null;
    }

    public void updateModelWithCutFromCore(HashMap<String, TransformedFormula> transformedFormulas, Witness liawitness, Context context, Solver solver, Model model) {
        String[] unsatCore = liawitness.getUnsatCore();
        addCutUnsatCoreGraeme(transformedFormulas, context, unsatCore, solver, model);
    }

    public BoolExpr addConstraintsToGurobiAndReturnAddedFormulas(HashMap<String, TransformedFormula> transformedFormulas,
            String[] currentAssumptions, GRBEnv env, GurobiInterface grbInterface, GRBModel grbModel, Context context, Z3Interface z3Interface, Model quotientModelA) {
        BoolExpr z3Formula;
        BoolExpr formulaUnderCurrentAss = context.mkTrue();
        int assSize = currentAssumptions.length;
        String id;
        if (assSize > 0) {
            id = currentAssumptions[0];
            boolean isTrueFormula = transformedFormulas.get(id).getOriginalFormula().isTrue();
            if (!isTrueFormula) {
                z3Formula = addConstraintToGrbSolver(transformedFormulas, id, grbModel,
                        env, grbInterface, context, z3Interface, quotientModelA, refinementCount);
                // System.out.println("z3formula ==========" + z3Formula);
                if (!z3Formula.isTrue()) {
                    formulaUnderCurrentAss = z3Formula;
                }
            }
        }
        for (int i = 1; i < assSize; i++) {
            id = currentAssumptions[i];
            boolean isTrueFormula = transformedFormulas.get(id).getOriginalFormula().isTrue();
            if (!isTrueFormula) {
                z3Formula = addConstraintToGrbSolver(transformedFormulas, id, grbModel, env, grbInterface, context, z3Interface, quotientModelA, refinementCount);
                //System.out.println("z3formula1 ==========" + z3Formula);
                if (!z3Formula.isTrue()) {
                    formulaUnderCurrentAss = context.mkAnd(formulaUnderCurrentAss, z3Formula);
                }
            }
        }
        return formulaUnderCurrentAss;
    }

    public BoolExpr getFormulaWVarBounds(BoolExpr be, Context context, Z3Interface z3Interface) {
        HashSet<IntExpr> intvars = Util.collectIntVars(be);
        HashSet<BvVariable> variablesF = convertIntVarsToBvVars(intvars, context);
        be = context.mkAnd(be, genVarsBounds(context, variablesF, new HashSet<>()));
        //simplifying the formula a bit before passing to a quanfier elimination procedrue
        //be = z3Interface.simplifyQFLIAFormula(context, be);
        return be;
    }

    BoolExpr collectDeltaFreeFormulasFromCurrentAssumption(HashMap<String, TransformedFormula> transformedFormulas, String[] currentAssumption, Context context, Z3Interface z3Interface) {
        BoolExpr qfFormula = context.mkTrue();
        BoolExpr tempFormula;
        boolean firstQFFormulaFound = false;
        for (String id : currentAssumption) {
            TransformedFormula tf = transformedFormulas.get(id);
            if (tf.isPrecise() && tf.deltaIntroduced) {
                tempFormula = tf.getArithFormulaWoDeltas(); //this is delta free formula needed for qe elimination
                if (tempFormula == null) { //generate delta free formula which is not introduced so far
                    tempFormula = z3Interface.eliminateQuantifiers(context, tf.getArithExprWQuantDeltas());
                    tf.setArithFormulaWoDeltas(tempFormula);
                }
                //the purpose of the following condition is to avoid (and true ..
                if (!firstQFFormulaFound) {
                    qfFormula = tempFormula;
                    firstQFFormulaFound = true;
                } else {
                    qfFormula = context.mkAnd(qfFormula, tempFormula);
                }
            }
        }
        return qfFormula;
    }

    public BoolExpr removeQuantifiersFrom(BoolExpr formulaUnderCurrentAss, Context context, Sort[] boundVarSorts, Symbol[] boundVarNames, Z3Interface z3Interface) {
        //System.out.println("formula under current " + formulaUnderCurrentAss);
        HashSet<IntExpr> intvars = Util.collectIntVars(formulaUnderCurrentAss);
        HashSet<BvVariable> variablesF = convertIntVarsToBvVars(intvars, context);
        formulaUnderCurrentAss = context.mkAnd(formulaUnderCurrentAss, genVarsBounds(context, variablesF, new HashSet<>()));
        //simplifying the formula a bit before passing to a quanfier elimination procedrue
        formulaUnderCurrentAss = z3Interface.simplifyQFLIAFormula(context, formulaUnderCurrentAss);
        formulaUnderCurrentAss = getFormulaWBoundVars(context, formulaUnderCurrentAss, boundVarNames);
        //add quantification
        formulaUnderCurrentAss = context.mkExists(boundVarSorts, boundVarNames, formulaUnderCurrentAss, 0, null, null, null, null);
        //eliminate quantifiers
        return z3Interface.eliminateQuantifiers(context, formulaUnderCurrentAss);

    }

    public Sort[] convertBVSort2IntSort(Sort[] bvSort, Context ctx) {
        int size = bvSort.length;
        Sort[] intSortList = new Sort[size];
        for (int i = 0; i < size; i++) {
            intSortList[i] = ctx.mkIntSort();
        }
        return intSortList;
    }

    public BoolExpr getFormulaWBoundVars(Context ctx, BoolExpr formula, Symbol[] varNames) {
        int nrBoundVars = varNames.length;
        Expr[] varExpr = new Expr[nrBoundVars];
        Expr[] boundedVars = new Expr[nrBoundVars];
        //reversal is necessary, because quantifiers are numbered inside out
        for (int i = 0; i < nrBoundVars; i++) {
            varExpr[nrBoundVars - 1 - i] = ctx.mkIntConst(varNames[i]); //reversing the list
        }
        IntSort is = ctx.mkIntSort();
        for (int i = 0; i < nrBoundVars; i++) {
            boundedVars[i] = ctx.mkBound(i, is); //reversing the list
        }
        return (BoolExpr) formula.substitute(varExpr, boundedVars);
    }

    public BoolExpr addConstraintToGrbSolver(HashMap<String, TransformedFormula> transformedFormulas, String formulaId, GRBModel grbModel, GRBEnv env, GurobiInterface grbInterface, Context context, Z3Interface z3Interface, Model deltaModel, int refinementCount) {
        BoolExpr z3Formula = context.mkTrue();
        ArrayList<BoolExpr> simplifiedFormula = null;
        TransformedFormula tf = transformedFormulas.get(formulaId);
        int nrConstraints = tf.getFormulaSize();
        boolean alreadyInSolver = tf.isAlreadyInTransformedFormInThesolver();
        if (alreadyInSolver && !tf.isPrecise()) {
            //constraint is already in the solver, remove them except precise ones
            for (int i = 0; i < nrConstraints; i++) {
                String idNew = formulaId + "__r__" + i;
                grbInterface.removeConstraint(grbModel, idNew);
            }
            if (tf.isPrecise()) {
                simplifiedFormula = extractBoolFormula(tf.getFormula(), context, deltaModel);
            } else {
                simplifiedFormula = selectQuotient(transformedFormulas, formulaId, context, deltaModel);
            }
            //System.out.println("simplified formula " + simplifiedFormula);
            grbModel = new Util().addListConstrsGRB(simplifiedFormula, grbModel, formulaId, z3GRBVarMap);
            tf.setAlreadyInTransformedFormInThesolver(true);
        } else if (!alreadyInSolver) { //delta model will not change and the constraint can stay in the solver
            if (tf.isPrecise()) {
                simplifiedFormula = extractBoolFormula(tf.getFormula(), context, deltaModel);
            } else {
                simplifiedFormula = selectQuotient(transformedFormulas, formulaId, context, deltaModel);
            }
            grbModel = new Util().addListConstrsGRB(simplifiedFormula, grbModel, formulaId, z3GRBVarMap);
            tf.setAlreadyInTransformedFormInThesolver(true);
        }
        if (!tf.isPrecise()) {
            if (simplifiedFormula != null) {
                for (BoolExpr be : simplifiedFormula) {
                    z3Formula = context.mkAnd(z3Formula, be);
                }
            }
        }
        simplifiedFormula = null; //releasing memory
        //no change to grbmodel in other cases
        return (BoolExpr) z3Formula.simplify();
    }

    public GRBModel refineModel(HashMap<String, TransformedFormula> transformedFormulas, String[] unsatCore, GRBModel grbModel, GRBEnv env, GurobiInterface grbInterface, Context context, Z3Interface z3Interface, Solver deltaSolver, Model deltaModel, int refinementCount) {
        addCutUnsatCoreGraeme(transformedFormulas, context, unsatCore, deltaSolver, deltaModel);
        deltaValuesModified = true;
        return grbModel; //means, the constraints are added normally
    }

    public BoolExpr blockPreviousModel(HashMap<String, TransformedFormula> transformedFormulas, Context ctx, Solver solver, Model model, String[] currentAssumptions, BoolExpr currentAssBoolExpr) {
        BoolExpr acc = ctx.mkTrue();
        TransformedFormula tf;
        ArithExpr deltaExpr;
        String s;
        //check if putting currentAssumptions instead of transformedFormulasA.keySet would be fine
        for (String s1 : currentAssumptions) {
            s = mapIdToOriginal(ctx, s1);
            tf = transformedFormulas.get(s);
            if (tf.deltaIntroduced) {
                deltaExpr = tf.formula.get(0).deltaExpr;
                //there are two choices whether deltaExpr is "-" or a single int expr
                if (deltaExpr.isSub()) {
                    Expr[] exprs = deltaExpr.getArgs();
                    acc = ctx.mkAnd(acc, ctx.mkEq(exprs[0], Z3Interface.evalExprInModel(model, exprs[0])));
                    acc = ctx.mkAnd(acc, ctx.mkEq(exprs[1], Z3Interface.evalExprInModel(model, exprs[1])));
                } else {
                    acc = ctx.mkAnd(acc, ctx.mkEq(deltaExpr, Z3Interface.evalExprInModel(model, deltaExpr)));
                }
            } else if (tf.isPrecise() || !tf.isDeltaIntroduced()) {
                acc = ctx.mkAnd(acc, idStringToBoolExpr.get(s));
            }
        }
        acc = (BoolExpr) ctx.mkNot(acc).simplify();//put not
        BoolExpr notCurrentDeltas = ctx.mkImplies(currentAssBoolExpr, acc);
        return notCurrentDeltas;
    }

    String[] getCurrentAssumptionUnder(HashMap<String, TransformedFormula> transformedFormulas, Model m, Context context, Boolean isAssumptionA) {
        BoolExpr assumptionFormula = context.mkTrue();
        ArrayList<String> assumptions = new ArrayList<>();
        Iterator<String> constrIds = transformedFormulas.keySet().iterator();
        BoolExpr boolId;
        String s;
        while (constrIds.hasNext()) {
            s = constrIds.next();
            boolId = getIdsBoolExpr(s, context);
            if (Z3Interface.evalExprInModel(m, boolId).isTrue()) {
                assumptions.add(s);
                assumptionFormula = boolId;
                break;
            };
        }
        while (constrIds.hasNext()) {
            s = constrIds.next();
            boolId = getIdsBoolExpr(s, context);
            if (Z3Interface.evalExprInModel(m, boolId).isTrue()) {
                assumptions.add(s);
                assumptionFormula = context.mkAnd(assumptionFormula, boolId);
            };
        }
        if (isAssumptionA) {
            cutAssumptionsA = assumptionFormula;
        } else {
            cutAssumptionsB = assumptionFormula;
        }

        return assumptions.toArray(new String[assumptions.size()]);

    }

    public BoolExpr stringListToBF(Context ctx, String[] liaFormulas) {
        BoolExpr acc = ctx.mkTrue();
        if (liaFormulas.length > 0) {
            acc = getIdsBoolExpr(liaFormulas[0], ctx);
        }
        for (int i = 1; i < liaFormulas.length; i++) {
            acc = ctx.mkAnd(acc, getIdsBoolExpr(liaFormulas[i], ctx));
        }
        return acc;
    }

    public BoolExpr translateBvToMlia(BoolExpr bvFormula, Context context, Z3Interface z3Interface, PreProcessBV ppBV) {
        BoolExpr returnExpr;
//        returnExpr = z3Interface.getNNF(context, bvFormula);
        //translate bit-vector formulas to modulo integer formulas
        if (!bvFormula.isQuantifier()) {
            returnExpr = z3Interface.getNNF(context, bvFormula);
            returnExpr = ppBV.translateToLIA(context, bvFormula);
            return returnExpr;
        }
        //has a quantifier and converting to nnf does not work in the presence of quantifiers
        BoolExpr preProcessedFormula = bvFormula;
        //the formula contains quantifier
        Quantifier q = (Quantifier) preProcessedFormula;
        Symbol[] varNames = q.getBoundVariableNames(); //bound variable are ordered top-down
        Sort[] varSorts = q.getBoundVariableSorts();
        int nrBoundVars = varNames.length;
        Expr[] bvVarExpr = new Expr[nrBoundVars];
        for (int i = 0; i < varNames.length; i++) {
            bvVarExpr[nrBoundVars - 1 - i] = context.mkBVConst(varNames[i], ((BitVecSort) varSorts[i]).getSize()); //change it with appropriate bit
        }
        BoolExpr qBody = q.getBody();
        qBody = (BoolExpr) qBody.substituteVars(bvVarExpr);
        //System.out.println("nnf " + qBody);
        qBody = getFormulaWBoundVars(context, qBody, varNames);
        qBody = z3Interface.getNNF(context, qBody);
        //System.out.println("translate to nnf "+qBody);
        returnExpr = context.mkExists(bvVarExpr, qBody, 0, null, null, null, null);
        returnExpr = ppBV.translateToLIA(context, returnExpr);
        //System.out.println("lia expr " + returnExpr);
        return returnExpr;
    }

    public BoolExpr simplifyQOrQFBVFormula(BoolExpr bExpr, Context context) {
        if (!bExpr.isQuantifier()) {
            //the formula is already quantifier free
            // bExpr = translateBvToMlia(bExpr, context, z3Interface, ppBV);
            return bExpr;
        }
        BoolExpr preProcessedFormula = bExpr;
        //the formula contains quantifier
        Quantifier q = (Quantifier) preProcessedFormula;
        Symbol[] varNames = q.getBoundVariableNames(); //bound variable are ordered top-down
        Sort[] varSorts = q.getBoundVariableSorts();
        int nrBoundVars = varNames.length;
        Expr[] bvVarExpr = new Expr[nrBoundVars];
        for (int i = 0; i < varNames.length; i++) {
            bvVarExpr[nrBoundVars - 1 - i] = context.mkBVConst(varNames[i], ((BitVecSort) varSorts[i]).getSize()); //change it with appropriate bit
        }
        BoolExpr qBody = q.getBody();
        qBody = (BoolExpr) qBody.substituteVars(bvVarExpr);
        Z3Interface z3Interface = new Z3Interface();
        qBody = z3Interface.preProcessQFBVFormulasForQE(context, qBody);
        //System.out.println("qbody =================\n" + qBody);
//TODO: remove quantified variables which are not in the formula
        //put back quantifiers
        qBody = getFormulaWBoundVars(context, qBody, varNames);
        bExpr = context.mkExists(bvVarExpr, qBody, 0, null, null, null, null);
        preProcessedFormula = z3Interface.preProcessQBVFormulasForQE(context, bExpr);
        return preProcessedFormula;
    }

    public BoolExpr simplifyQBVFormula(BoolExpr bExpr, Context context, Z3Interface z3Interface, PreProcessBV ppBV) {
        if (!bExpr.isQuantifier()) {
            //the formula is already quantifier free
            //bExpr = translateBvToMlia(bExpr, context, z3Interface, ppBV);
            return bExpr;
        }
        BoolExpr preProcessedFormula = bExpr;
        //the formula contains quantifier
        preProcessedFormula = z3Interface.preProcessQBVFormulasForQE(context, bExpr);
        //preProcessedFormula = translateBvToMlia(preProcessedFormula, context, z3Interface, ppBV);
        return preProcessedFormula;
    }

    public BoolExpr preProcessQBVFormula(BoolExpr bExpr, Context context) {
        if (Main.SMT_LOGIC.equals("QF_BV") || Main.SMT_LOGIC.equals("QF_AUFBV") || Main.SMT_LOGIC.equals("BV")) {
            return simplifyQOrQFBVFormula(bExpr, context);
        } else {
            return bExpr;
        }
    }

    public LinkedHashMap<String, TransformedFormula> copyTranformedFormulaBtoA(LinkedHashMap<String, TransformedFormula> transformedFormulasA, LinkedHashMap<String, TransformedFormula> transformedFormulasB) {
        Set<String> keysB = transformedFormulasB.keySet();
        for (String s : keysB) {
            transformedFormulasA.put(s, transformedFormulasB.get(s));
        }
        return transformedFormulasA;
    }

    public void tranformAndStoreFormulas(HashMap<String, TransformedFormula> transformedFormulas, GRBModel grbModel, Context context, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, Solver quotientSolver) {
        Set<String> constraints = transformedFormulas.keySet();
        TransformedFormula tf;
        for (String id : constraints) {
            tf = getTransformedFormula(transformedFormulas, grbModel, context, id, z3Interface, grbInterface, env, quotientSolver);
            transformedFormulas.put(id, tf);
        }
    }

    public BoolExpr interpolantMAFromFormula(BoolExpr formulaA, BoolExpr formulaB, InterpolationContext context) {
        try {
            Z3Interface z3Interface = new Z3Interface();
            GurobiInterface grbInterface = new GurobiInterface();
            GRBEnv env = grbInterface.createGRBEnv();

            Solver solverA = z3Interface.createMinimalModelProdSolver(context);
            Solver solverB = z3Interface.createMinimalModelProdSolver(context);
            //boolStructure captures the boolean structure of the formula
            BoolExpr boolStructureA = assignIdToBVFormula(formulaA, context, transformedFormulasA, solverA);
            BoolExpr boolStructureB = assignIdToBVFormula(formulaB, context, transformedFormulasB, solverB);//we put all into the solver A and later copy to solver B
//            Util.print(PRINT_FLAG, "finished identifying");
            //solverA.add(context.mkAnd(boolStructureA, boolStructureB));
            solverA.add(boolStructureA);
            solverB.add(boolStructureB);
            GRBModel grbModelA = grbInterface.getGRBModel(env);
            GRBModel grbModelB = grbInterface.getGRBModel(env);
            sizeIntVar = getVarsSizeMap(vars, context);
            Util.createZ3GRBVarMap(grbModelA, vars, z3GRBVarMap, context);
            grbInterface.updateModel(grbModelA); // update gurobi model after variable addition
            Util.createZ3GRBVarMap(grbModelB, vars, z3GRBVarMap, context);
            grbInterface.updateModel(grbModelB); // update gurobi model after variable addition
            //copy transformedFormulasB to A
            //transformedFormulasA = copyTranformedFormulaBtoA(transformedFormulasA, transformedFormulasB);
            tranformAndStoreFormulas(transformedFormulasA, grbModelA, context, z3Interface, grbInterface, env, solverA);
            tranformAndStoreFormulas(transformedFormulasB, grbModelB, context, z3Interface, grbInterface, env, solverB);
            BoolExpr interpolantFormula = (BoolExpr) computeInterpolantTransformedFormula(z3Interface, context, env, grbInterface, solverA, solverB, grbModelA, grbModelB).simplify();
            z3Interface = null;
            return interpolantFormula;
        } catch (Z3Exception ex) {
            ex.printStackTrace();
        } catch (Exception e) {
            e.printStackTrace();
        }
        return null;
    }

    //assumes the conjunciton of formulaA and formulaB is unsat
    //returns null if one the the pre-processed formula is not trivially true or false
//    public BoolExpr getInterpolantByPreProcessingFormulas(BoolExpr formulaA, BoolExpr formulaB, Context ctx, Z3Interface z3Interface) {
//        BoolExpr ppFormulaA = z3Interface.preProcessQFBVFormulas(ctx, formulaA);
//        if (ppFormulaA.isFalse()) {
//            return ctx.mkFalse();
//        }
//        BoolExpr ppFormulaB = z3Interface.preProcessQFBVFormulas(ctx, formulaB);
//        if (ppFormulaA.isTrue()) {
//            if (ppFormulaB.isFalse()) {
//                return ctx.mkTrue();
//            } else { //the formula can be satisfiable, since we could not prove the unsat of ppFormulaB
//                return null;
//            }
//        }
//        if (ppFormulaB.isFalse()) {
//            return ctx.mkTrue();
//        }
//        if (ppFormulaA.isTrue()) {
//            if (ppFormulaA.isFalse()) {
//                return ctx.mkFalse();
//            }else{ //the formula can be satisfiable, since we could not prove the unsat of ppFormulaB
//                return null;
//            }
//        }
//        return null;
//    }
    public BoolExpr getInterpolantByPreProcessingFormulas(BoolExpr formulaA, BoolExpr formulaB, Context ctx, Z3Interface z3Interface) {
        formulaA = z3Interface.preProcessQFBVFormulas(ctx, formulaA);
        if (formulaA.isFalse()) {
            return ctx.mkFalse();
        }
        formulaB = z3Interface.preProcessQFBVFormulas(ctx, formulaB);
        if (formulaA.isTrue()) {
            if (formulaB.isFalse()) {
                return ctx.mkTrue();
            }
        }
        if (formulaB.isFalse()) {
            return ctx.mkTrue();
        }
        if (formulaB.isTrue()) {
            if (formulaA.isFalse()) {
                return ctx.mkFalse();
            }
        }
        return null;
    }

    public BoolExpr interpolantMAFromFile(String inputFile) {
        //initiate garbage collector
        System.gc();
        Z3Interface z3Interface = new Z3Interface();
        InterpolationContext context = z3Interface.getInerpolationContext();
        //BoolExpr bExpr = z3Interface.readSMTInputWSymbols(inputFile, new FuncDecl[]{getInterpolants} , context);
        BoolExpr bExpr = z3Interface.readSMTInputWSymbols(inputFile, null, context);
        Expr[] formulaAandFormulaB = z3Interface.getFormulasAandB(bExpr);
        BoolExpr formulaA = (BoolExpr) formulaAandFormulaB[0];
        BoolExpr formulaB = (BoolExpr) formulaAandFormulaB[1];
        //pre-process formula A and B, if they trivally return true or false then return interpolant from there
        BoolExpr interpolantByPP = getInterpolantByPreProcessingFormulas(formulaA, formulaB, context, z3Interface);
        if (interpolantByPP != null) {
            System.out.println("interpolants were derived from pre-processing");
            return interpolantByPP;
        }
        //System.out.println("new formulaa "+formulaA);
        //System.out.println("new formulaB "+formulaB);
        //z3Interface.solveBVTactic(formulaA, context);
        return interpolantMAFromFormula(formulaA, formulaB, context);
    }

    public HashMap<IntExpr, Integer> getVarsSizeMap(HashSet<BvVariable> bvVars, Context ctx) {
        HashMap<IntExpr, Integer> varSizeMap = new HashMap<>();
        for (BvVariable bvVar : bvVars) {
            varSizeMap.put(ctx.mkIntConst(bvVar.getName()), bvVar.getSortSize());
        }
        return varSizeMap;
    }

    public Delta[] getDeltaValues(Delta[] deltaParams, Model deltaModel, Context context, Z3Interface z3Interface) {
        Delta[] deltaValues = new Delta[2];
        IntExpr d1, d2;
        if (deltaParams[0] != null) {
            d1 = (IntExpr) z3Interface.evalExprInModel(deltaModel, deltaParams[0].getVar());
            deltaValues[0] = new Delta(deltaParams[0].getVar(), d1);
        } else {
            deltaValues[0] = null;
        }
        if (deltaParams[1] != null) {
            d2 = (IntExpr) z3Interface.evalExprInModel(deltaModel, deltaParams[1].getVar());
            deltaValues[1] = new Delta(deltaParams[1].getVar(), d2);
        } else {
            deltaValues[1] = null;
        }
        return deltaValues;

    }

    public ArrayList<BoolExpr> extractBoolFormula(ArrayList<ArithFormula> arithFormulas, Context context, Model deltaModel) {
        ArrayList<BoolExpr> booleanFormula = new ArrayList<>();
        BoolExpr beEval;
//            System.out.println("arith for "+arithFormulas.get(0).formula);
        int length = arithFormulas.size();
        for (int i = 0; i < length; i++) {
            ArithFormula af = arithFormulas.get(i);
            beEval = af.getFormula();
            if (beEval.isFalse()) { //the whole formula is not feasible
                ArrayList<BoolExpr> falseF = new ArrayList<>();
                falseF.add(beEval);
                return falseF;
            } else {
                if (!beEval.isTrue()) {
                    booleanFormula.add(beEval);
                }
            }
        }
        return booleanFormula;
    }

    public ArrayList<BoolExpr> selectQuotient(HashMap<String, TransformedFormula> transformedFormulas, String id, Context context, Model deltaModel) {
        ArrayList<BoolExpr> formulasWFixedCoeffs = new ArrayList<>();
        TransformedFormula tf = transformedFormulas.get(id);
        BoolExpr beEval;
        ArrayList<ArithFormula> arithFormulas = tf.getFormula();
//            System.out.println("arith for "+arithFormulas.get(0).formula);
        int length = arithFormulas.size();
        for (int i = 0; i < length; i++) {
            ArithFormula af = arithFormulas.get(i);
            beEval = (BoolExpr) Z3Interface.evalExprInModelWoMc(deltaModel, af.getFormula());
            if (beEval.isFalse()) { //the whole formula is not feasible
                formulasWFixedCoeffs.add(beEval);
                break;
            } else {
                if (!beEval.isTrue()) {
                    formulasWFixedCoeffs.add(beEval);
                }
            }
        }
        return formulasWFixedCoeffs;
    }

    //formula is a atomic bv-formula
    public int findBVSizeFrom(BoolExpr atomicBVFormula) {
        if (atomicBVFormula.isConst()) {
            //return maximum size for BV
            return Main.DEFAULT_BIT;
        } else {
            BitVecExpr bvExpr = (BitVecExpr) atomicBVFormula.getArgs()[0];
            return bvExpr.getSortSize();

        }
    }

    public TransformedFormula getTransFormulaCorrespondingToBooleanConstants(GRBModel grbModel, Context context, TransformedFormula tf, Z3Interface z3Interface,
            GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {
        BoolExpr formula = tf.getOriginalFormula();
        tf.setAlreadyInTransformedFormInThesolver(false); //at the beginning a constrint is not in transformed form in the solver
        if (formula.isTrue()) { //this formula plays no role in the satisfiability
            return tf;
        }
        IntExpr zero = context.mkInt(0);
        IntExpr one = context.mkInt(1);
        ArrayList<ArithFormula> arithFormulas = new ArrayList<>();
        if (formula.isFalse()) { //this just makes model infesible
            BoolExpr exprFalse = context.mkLe(one, zero);
            arithFormulas.add(new ArithFormula(exprFalse, zero, false));
            tf.setFormula(arithFormulas);
            tf.setFormulaSize(1);
            return tf;
        }
        return null;
    }

    public TransformedFormula getTransFormulaWithBothDeltas(IntExpr delta0, IntExpr delta1, String id, BoolExpr maExpr, BoolExpr finalLIAExpr, int sortSize, TransformedFormula tf, ArrayList<ArithFormula> arithFormulas, BoolExpr simplifiedAaExpr,
            GRBModel grbModel, Context context, Solver deltaSolver, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, PreProcessBV ppbv) {
        BoolExpr deltaBounds, deltaBounds1, deltaBounds2;
        String inEqSign = getIneqSign(maExpr);
        boolean isEq = maExpr.isEq();
        Expr[] exprs = maExpr.getArgs();
        ArithExpr deltaExpr = getDeltaExprCut(delta0, delta1, inEqSign, context);
        arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
        BoolExpr beLo0 = genLoBound(context, (ArithExpr) exprs[0], sortSize);
        arithFormulas.add(new ArithFormula(beLo0, deltas[0], false));
        BoolExpr beUp0 = genUpBound(context, (ArithExpr) exprs[0], sortSize);
        arithFormulas.add(new ArithFormula(beUp0, context.mkUnaryMinus(deltas[0]), false));

        BoolExpr beLo1 = genLoBound(context, (ArithExpr) exprs[1], sortSize);
        arithFormulas.add(new ArithFormula(beLo1, deltas[1], false));
        BoolExpr beUp1 = genUpBound(context, (ArithExpr) exprs[1], sortSize);
        arithFormulas.add(new ArithFormula(beUp1, context.mkUnaryMinus(deltas[1]), false));

        finalLIAExpr = (BoolExpr) context.mkAnd(maExpr, beLo0, beUp0, beLo1, beUp1, finalLIAExpr).simplify();
        if (finalLIAExpr == context.mkFalse()) {
            // System.out.println("var bounds ======================================");
        }
        //TODO: if moduloExpr is false, then the formula is not consistent so it can be be replaced by false
        BoolExpr preProcessedExpr = z3Interface.inferDeltaBoundsfromAExpr(context, finalLIAExpr);
//            System.out.println("preprocessed expr ================= "+ preProcessedExpr);
        if (preProcessedExpr.isFalse()) {
            Expr[] origExprs = tf.getOriginalFormula().getArgs();
            deltaBounds1 = genOptDeltaBound(id, context, (BitVecExpr) origExprs[0], deltas[0], grbInterface, env, grbModel, deltaSolver, ppbv);
            deltaBounds2 = genOptDeltaBound(id, context, (BitVecExpr) origExprs[0], deltas[1], grbInterface, env, grbModel, deltaSolver, ppbv);
        } else {
            deltaBounds1 = z3Interface.getMaxMinDeltaExpr(grbModel, context, deltas[0], preProcessedExpr, z3GRBVarMap);
            deltaBounds2 = z3Interface.getMaxMinDeltaExpr(grbModel, context, deltas[1], preProcessedExpr, z3GRBVarMap);
            deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), deltaBounds1));
            deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), deltaBounds2));
        }
        deltaBounds = context.mkAnd(deltaBounds1, deltaBounds2);
//        System.out.println("delta bounds both =========="+deltaBounds);
        BoolExpr fullLiaExr = context.mkAnd(finalLIAExpr, deltaBounds);
        BoolExpr deltaQuantExpr = getDeltaQuantifiedExpression(deltas[0], deltas[1], fullLiaExr, context, z3Interface);
        tf.setArithExprWQuantDeltas(deltaQuantExpr);
//        if (tf.isPrecise()) {
//            tf.setArithFormulaWoDeltas(fullLiaExr);
//        }
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(5);
        return tf;
    }

    //returns null if the formula if false, returns the same TransformedFormula if the formula is true, the input if bv-inequation (does not contain not or equality)
    public TransformedFormula getTransformedFormula(HashMap<String, TransformedFormula> transformedFormulas, GRBModel grbModel, Context context, String id, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver) {
        IntExpr zero = context.mkInt(0);
        TransformedFormula tf = transformedFormulas.get(id);
        BoolExpr formula = tf.getOriginalFormula();
        int sortSize = findBVSizeFrom(formula);
        if (sortSize <= Main.THRESHOLD_BIT) {
            tf.setPrecise(true);
        }
        tf.setStatus(1); //transformed
        //tf.setFormulaWModulo(genModuloArithInEq(context, formula));
        tf.setAlreadyInTransformedFormInThesolver(false); //at the beginning a constrint is not in transformed form in the solver
        if (formula.isTrue() || formula.isFalse()) { //this formula plays no role in the satisfiability
            return getTransFormulaCorrespondingToBooleanConstants(grbModel, context, tf, z3Interface, grbInterface, env, deltaSolver);
        }
        ArrayList<ArithFormula> arithFormulas = new ArrayList<>();
        PreProcessBV ppbv = new PreProcessBV();
        BoolExpr maExpr = genAinEqFromAtomicBvinEq(context, id, formula, z3Interface, grbModel, grbInterface, env, deltaSolver, ppbv);
//        System.out.println("ma expr "+maExpr);
        BoolExpr moduloExpr = genVarsBounds(context, Util.collectBvVars(formula, context), new HashSet<>()); //this will have all the constraints
        String inEqSign = getIneqSign(maExpr);
        boolean isEq = maExpr.isEq();
        BoolExpr simplifiedAaExpr = Z3Interface.standariseArithInEq(maExpr, context);
        Expr[] exprs = maExpr.getArgs();

        if (deltas[0] != null && deltas[1] != null) {
            tf.setDeltaIntroduced(true);
            return getTransFormulaWithBothDeltas(deltas[0], deltas[1], id, maExpr, moduloExpr, sortSize, tf, arithFormulas, simplifiedAaExpr, grbModel,
                    context, deltaSolver, z3Interface, grbInterface, env, ppbv);
        }

        if (deltas[0] != null) {
            tf.setDeltaIntroduced(true);
            Expr[] origExprs = tf.getOriginalFormula().getArgs();
            return getTransFormulaLeftDelta(grbModel, id, inEqSign, isEq, sortSize, tf, maExpr, (ArithExpr) exprs[0], simplifiedAaExpr, deltas[0], zero, moduloExpr,
                    (BitVecExpr) origExprs[0], context, z3Interface, grbInterface, env, deltaSolver, arithFormulas, ppbv);
        }
        if (deltas[1] != null) {
            tf.setDeltaIntroduced(true);
            Expr[] origExprs = tf.getOriginalFormula().getArgs();
            return getTransFormulaRightDelta(grbModel, id, inEqSign, isEq, sortSize, tf, maExpr, (ArithExpr) exprs[1], simplifiedAaExpr, zero, deltas[1],
                    moduloExpr, (BitVecExpr) origExprs[1], context, z3Interface, grbInterface, env, deltaSolver, arithFormulas, ppbv);
        }

        tf.setDeltaIntroduced(false); //no deltas were introduced
        tf.setArithFormulaWoDeltas(context.mkTrue()); //is LIA version of the original expr
        // in this case, both deltas are null
        //treatment of boolean variables
        if (simplifiedAaExpr.isConst() || simplifiedAaExpr.isBV()) { //boolean variable of bit-vector sort
            return getTranformedFormulaforBooeanVariable(tf, context, simplifiedAaExpr, arithFormulas);
        }
        //default case, where no deltas were introduced
        arithFormulas.add(new ArithFormula(simplifiedAaExpr, zero, isEq));
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(1);
        return tf;
    }

    public TransformedFormula getTransFormulaRightDelta(GRBModel grbModel, String id, String inEqSign, boolean isEq, int sortSize, TransformedFormula tf,
            BoolExpr maExpr, ArithExpr deltaInducingExpr, BoolExpr simplifiedAaExpr, IntExpr leftDelta, IntExpr rightDelta, BoolExpr moduloExpr,
            BitVecExpr origExprDeltaSide, Context context, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver,
            ArrayList<ArithFormula> arithFormulas, PreProcessBV ppbv) {
        BoolExpr deltaBounds;
        ArithExpr deltaExpr = getDeltaExprCut(leftDelta, rightDelta, inEqSign, context);
        arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
        BoolExpr beLo1 = genLoBound(context, (ArithExpr) deltaInducingExpr, sortSize);
        arithFormulas.add(new ArithFormula(beLo1, rightDelta, false));
        BoolExpr beUp1 = genUpBound(context, (ArithExpr) deltaInducingExpr, sortSize);
        arithFormulas.add(new ArithFormula(beUp1, context.mkUnaryMinus(rightDelta), false));

        moduloExpr = (BoolExpr) context.mkAnd(maExpr, beLo1, beUp1, moduloExpr).simplify();
        //TODO: if moduloExpr is false, then the formula is not consistent so it can be be replaced by false
        BoolExpr preProcessedExpr = z3Interface.inferDeltaBoundsfromAExpr(context, moduloExpr);
//             System.out.println("preprocessed expr ================= "+ preProcessedExpr);
        if (preProcessedExpr.isFalse()) {
//                System.out.println("is false 1 deltas");
            deltaBounds = genOptDeltaBound(id, context, origExprDeltaSide, rightDelta, grbInterface, env, grbModel, deltaSolver, ppbv);
        } else {
//                System.out.println("preproc expr  "+preProcessedExpr.isTrue());
            deltaBounds = z3Interface.getMaxMinDeltaExpr(grbModel, context, rightDelta, preProcessedExpr, z3GRBVarMap);
            deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), deltaBounds));
        }
//        System.out.println("delta bounds right =========="+deltaBounds);
        BoolExpr fullLiaExr = context.mkAnd(moduloExpr, deltaBounds);
        BoolExpr deltaQuantExpr = getDeltaQuantExpression(rightDelta, fullLiaExr, context, z3Interface);
        tf.setArithExprWQuantDeltas(deltaQuantExpr);
//        if (tf.isPrecise()) {
//            tf.setArithFormulaWoDeltas(fullLiaExr);
//        } //else needs quantifier elimination so do not do it on demand
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(3);
        return tf;
    }

    public TransformedFormula getTransFormulaLeftDelta(GRBModel grbModel, String id, String inEqSign, boolean isEq, int sortSize, TransformedFormula tf,
            BoolExpr maExpr, ArithExpr deltaInducingExpr, BoolExpr simplifiedAaExpr, IntExpr leftDelta, IntExpr rightDelta, BoolExpr moduloExpr,
            BitVecExpr origExprDeltaSide, Context context, Z3Interface z3Interface, GurobiInterface grbInterface, GRBEnv env, Solver deltaSolver,
            ArrayList<ArithFormula> arithFormulas, PreProcessBV ppbv) {
        BoolExpr deltaBounds;
        ArithExpr deltaExpr = getDeltaExprCut(leftDelta, rightDelta, inEqSign, context);
        arithFormulas.add(new ArithFormula(simplifiedAaExpr, deltaExpr, isEq));
        BoolExpr beLo1 = genLoBound(context, (ArithExpr) deltaInducingExpr, sortSize);
        arithFormulas.add(new ArithFormula(beLo1, leftDelta, false));
        BoolExpr beUp1 = genUpBound(context, (ArithExpr) deltaInducingExpr, sortSize);
        arithFormulas.add(new ArithFormula(beUp1, context.mkUnaryMinus(leftDelta), false));

        moduloExpr = (BoolExpr) context.mkAnd(maExpr, beLo1, beUp1, moduloExpr).simplify();
        //TODO: if moduloExpr is false, then the formula is not consistent so it can be be replaced by false
        BoolExpr preProcessedExpr = z3Interface.inferDeltaBoundsfromAExpr(context, moduloExpr);
//             System.out.println("preprocessed expr ================= "+ preProcessedExpr);
        if (preProcessedExpr.isFalse()) {
//                System.out.println("is false 1 deltas");
            deltaBounds = genOptDeltaBound(id, context, origExprDeltaSide, leftDelta, grbInterface, env, grbModel, deltaSolver, ppbv);
        } else {
//                System.out.println("preproc expr  "+preProcessedExpr.isTrue());
            deltaBounds = z3Interface.getMaxMinDeltaExpr(grbModel, context, leftDelta, preProcessedExpr, z3GRBVarMap);
            deltaSolver.add(context.mkImplies(idStringToBoolExpr.get(id), deltaBounds));
        }
//        System.out.println("delta bounds left =========="+deltaBounds);
        BoolExpr fullLiaExr = context.mkAnd(moduloExpr, deltaBounds);
        BoolExpr deltaQuantExpr = getDeltaQuantExpression(leftDelta, fullLiaExr, context, z3Interface);
        tf.setArithExprWQuantDeltas(deltaQuantExpr);
//        if (tf.isPrecise()) {
//            tf.setArithFormulaWoDeltas(fullLiaExr);
//        }
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(3);
        return tf;
    }

    public BoolExpr getDeltaQuantExpression(IntExpr delta, BoolExpr fullLiaExr, Context ctx, Z3Interface z3Interface) {
        Sort[] sorts = new Sort[1];
        sorts[0] = ctx.mkIntSort();
        Symbol[] symbols = new Symbol[1];
        symbols[0] = ctx.mkSymbol(delta.toString());
        fullLiaExr = getFormulaWBoundVars(ctx, fullLiaExr, symbols);
        BoolExpr quantExpr = ctx.mkExists(sorts, symbols, fullLiaExr, 0, null, null, null, null);
        return quantExpr;
        //return z3Interface.eliminateQuantifiers(ctx, quantExpr);
    }

    public BoolExpr getDeltaQuantifiedExpression(IntExpr delta1, IntExpr delta2, BoolExpr fullLiaExr, Context ctx, Z3Interface z3Interface) {
        Sort[] sorts = new Sort[2];
        sorts[0] = ctx.mkIntSort();
        sorts[1] = ctx.mkIntSort();
        Symbol[] symbols = new Symbol[2];
        symbols[0] = ctx.mkSymbol(delta1.toString());
        symbols[1] = ctx.mkSymbol(delta2.toString());
        fullLiaExr = getFormulaWBoundVars(ctx, fullLiaExr, symbols);
        BoolExpr quantExpr = ctx.mkExists(sorts, symbols, fullLiaExr, 0, null, null, null, null);
        return quantExpr;
        //return z3Interface.eliminateQuantifiers(ctx, quantExpr);
    }

    public TransformedFormula getTranformedFormulaforBooeanVariable(TransformedFormula tf, Context context, BoolExpr simplifiedAaExpr, ArrayList<ArithFormula> arithFormulas) {
        IntExpr zero = context.mkInt(0);
        IntExpr one = context.mkInt(1);
        IntExpr binaryIntVariable = context.mkIntConst(simplifiedAaExpr.toString());
        BoolExpr loBoundvar, upBoundvar;
        loBoundvar = context.mkLe((ArithExpr) zero, binaryIntVariable);
        arithFormulas.add(new ArithFormula(loBoundvar, zero, false));
        upBoundvar = context.mkLe(binaryIntVariable, one);
        arithFormulas.add(new ArithFormula(upBoundvar, zero, false));
        tf.setFormula(arithFormulas);
        tf.setFormulaSize(2);
        return tf;
    }

    public void setVarBound(long lower, long upper, GRBModel model, String varName) {
        try {
            GRBVar grbVar = model.getVarByName(varName);
            grbVar.set(GRB.DoubleAttr.LB, (double) lower);
            grbVar.set(GRB.DoubleAttr.UB, (double) upper);
        } catch (GRBException e) {
            e.printStackTrace();
        }
    }

    public void setVariablesBound(GRBModel model, HashMap<IntExpr, GRBVar> z3GRBVarMap) {
        try {
            for (IntExpr ie : z3GRBVarMap.keySet()) {
                if (!boundedVars.contains(ie)) {
                    setVarBound(Util.min_neg(), Util.max_pos(), model, ie.getSExpr());
                    boundedVars.add(ie);
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public String mapIdToOriginal(Context ctx, String coreId) {
        //String[] result = new String[core.length];
        String suffix = "__r";
        String prefix = coreId;
        if (coreId.contains(suffix)) {//meaning the constraint was relaxed
            prefix = coreId.substring(0, coreId.indexOf(suffix)); //check this
        }
        return prefix;
    }

    public int getConstraintIndex(String coreId) {
        //String[] result = new String[core.length];
        String prefix = "__r__";
        String suffix = coreId.substring(coreId.indexOf(prefix) + 5); //check this
        return Integer.parseInt(suffix);
    }

    public String[] mapUnsatCoreIdsToOriginal(Context ctx, String[] core) {
        HashSet<String> resultH = new HashSet<>();
        for (int i = 0; i < core.length; i++) {
            String s = core[i];
            resultH.add(mapIdToOriginal(ctx, s));
        }
        String[] res = resultH.toArray(new String[resultH.size()]);
        resultH = null;
        return res;
    }

    public void addSoftConstraint(Context ctx, Solver solver, BoolExpr formula, BoolExpr conflictId) {
        String id = conflictId.getSExpr();
        BoolExpr newId = ctx.mkBoolConst(id + "_r");
        //logger.debug("refined formula: \n" + newId + ": " + formula);
        solver.add(ctx.mkImplies(newId, formula));
    }

    public BoolExpr[] replaceAssumption(BoolExpr[] assumptions, BoolExpr source, BoolExpr destination) {
        if (assumptions == null || (assumptions != null && assumptions.length == 0)) {
            return null;
        } else {
            int i = 0;
            while (i < assumptions.length) {
                //System.out.println("assumption= " + assumptions[i] + " souce= "+source);
                if (assumptions[i].equals(source)) {
                    assumptions[i] = destination;
                    return assumptions;
                }
                i++;
            }
            return assumptions;
        }
    }


    /* put the structure of the bool operations in disjSolver, list the rest of the formulas
     return type can be any boolean combination of ids, this method is tuned for modulo arithmetic
     also rewrite x*1 =< 1*y to x =< y
     */
    public BoolExpr assignIdToBVFormula(BoolExpr bExpr, Context ctx, LinkedHashMap<String, TransformedFormula> formulas, Solver disjSolver) {
        BoolExpr beId;
        BoolExpr andExpr = ctx.mkTrue();
        BoolExpr orExpr = ctx.mkFalse();
        Expr[] exprs;
        Expr auxBExpr;
        if (bExpr.isFalse()) {
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            disjSolver.add(ctx.mkImplies(idBe, ctx.mkFalse())); //so that it never comes in the model
            formulaCount++;
            formulas.put(id, new TransformedFormula(bExpr, 0, new HashSet<BvVariable>() {
            }));
            return idBe;
//            return ctx.mkImplies(idBe, bExpr); //avoiding this to appear in the boolean model
        }
        if (bExpr.isTrue()) { //do not add, it is already satisfied
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            formulaCount++;
            formulas.put(id, new TransformedFormula(bExpr, 0, new HashSet<BvVariable>() {
            }));
            return idBe;
        }
        if (bExpr.isNot()) { //assuming NNF
            auxBExpr = bExpr.getArgs()[0];
            return assignIdToNegatedFormula((BoolExpr) auxBExpr, ctx, formulas, disjSolver);
        }
        if (bExpr.isAnd()) {
            exprs = bExpr.getArgs();
            if (exprs.length > 0) {
                andExpr = assignIdToBVFormula((BoolExpr) exprs[0], ctx, formulas, disjSolver);
            }
            for (int i = 1; i < exprs.length; i++) {
                beId = assignIdToBVFormula((BoolExpr) exprs[i], ctx, formulas, disjSolver);
                andExpr = ctx.mkAnd(andExpr, beId);
            }
            return andExpr;
        }
        if (bExpr.isOr()) {
            exprs = bExpr.getArgs();
            if (exprs.length > 0) {
                orExpr = assignIdToBVFormula((BoolExpr) exprs[0], ctx, formulas, disjSolver);
            }
            for (int i = 1; i < exprs.length; i++) {
                beId = assignIdToBVFormula((BoolExpr) exprs[i], ctx, formulas, disjSolver);
                orExpr = ctx.mkOr(orExpr, beId);
            }
            return orExpr;
        }
        if (isBVOperation(bExpr)) {
            beId = assignIdToAtomicFormula(ctx, bExpr, formulas, true, disjSolver);
            return beId;
        }
        if (bExpr.isConst() && bExpr.isBool()) {
            //bExpr is a boolean variable
            beId = assignIdToAtomicFormula(ctx, bExpr, formulas, true, disjSolver);
            return beId;
        }
        System.out.println("Formula " + bExpr + " not recognized=== " + bExpr.isBVULE());
        return null;
    }

    //the formula auxBExpr is in NNF
    public BoolExpr assignIdToNegatedFormula(BoolExpr auxBExpr, Context ctx, LinkedHashMap<String, TransformedFormula> formulas, Solver disjSolver) {
        Expr[] auxExprs, arthiExprs;
        BoolExpr beId;
        if (auxBExpr.isFalse()) {//do nothing
//            Util.print(PRINT_FLAG, "false not  is the case=====");
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            formulaCount++;
            formulas.put(id, new TransformedFormula(ctx.mkTrue(), 0, new HashSet<BvVariable>() {
            }));
            return idBe;
        }
        if (auxBExpr.isTrue()) {
//            Util.print(PRINT_FLAG, "true not is the case ====");
            String id = "fmla_" + formulaCount;
            BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
            disjSolver.add(ctx.mkImplies(idBe, ctx.mkFalse()));
            formulaCount++;
            formulas.put(id, new TransformedFormula(ctx.mkFalse(), 0, new HashSet<BvVariable>() {
            }));
            return idBe;
//                return ctx.mkImplies(idBe, (BoolExpr) ctx.mkFalse()); //avoiding this to appear in the boolean model
        }
        if (auxBExpr.isConst() && auxBExpr.isBool()) { //is a boolean variable
            beId = assignIdToAtomicFormula(ctx, auxBExpr, formulas, true, disjSolver);
            return ctx.mkNot(beId);
        }
        if (auxBExpr.isEq()) { //this could well be boolean equality, assume BV for now
            auxExprs = auxBExpr.getArgs();
            beId = assignIdToBVFormula(ctx.mkOr(ctx.mkBVUGT((BitVecExpr) auxExprs[0], (BitVecExpr) auxExprs[1]), ctx.mkBVULT((BitVecExpr) auxExprs[0], (BitVecExpr) auxExprs[1])), ctx, formulas, disjSolver);
            return beId;
        }
        if (isBVOperation(auxBExpr)) {
            //can be <, <=, >, >=
            arthiExprs = auxBExpr.getArgs();
            BitVecExpr a0 = (BitVecExpr) arthiExprs[0];
            BitVecExpr a1 = (BitVecExpr) arthiExprs[1];
            BoolExpr retExpr;
            if (auxBExpr.isBVULT()) {
                retExpr = ctx.mkBVUGE(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isBVULE()) {
                retExpr = ctx.mkBVUGT(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isBVUGT()) {
                retExpr = ctx.mkBVULE(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
            if (auxBExpr.isBVUGE()) {
                retExpr = ctx.mkBVULT(a0, a1);
                beId = assignIdToAtomicFormula(ctx, retExpr, formulas, true, disjSolver);
                return beId;
            }
        }

        System.out.println("formula " + auxBExpr + " not recognized ");
        return null;

    }

    // tuned for modulo arithmetic
    public BoolExpr assignIdToAtomicFormula(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas, boolean isAtomic, Solver disjSolver) {
        //check for strict inequalities
        //is commented at the moment because it is easy to do so after the integer transformation
//        if (be.isBVULT()) {
//            Expr[] ineqExprs = be.getArgs();
//            BoolExpr retExpr1 = ctx.mkBVUGE((BitVecExpr) ineqExprs[1], ctx.mkInt(Util.min_neg() + 1));
//            BoolExpr retExpr2 = ctx.mkBVULE((BitVecExpr) ineqExprs[0], ctx.mkSub((BitVecExpr) ineqExprs[1], ctx.mkInt(1)));
//            BoolExpr retExpr = ctx.mkAnd(retExpr1, retExpr2);
//            return assignIdToBVFormula(retExpr, ctx, formulas, disjSolver);
//        }
//        if (be.isBVUGT()) {
//            Expr[] ineqExprs = be.getArgs();
//            BoolExpr retExpr1 = ctx.mkBVUGE((BitVecExpr) ineqExprs[0], ctx.mkInt(Util.min_neg() + 1));
//            BoolExpr retExpr2 = ctx.mkBVUGE(ctx.mkBVUSub((BitVecExpr) ineqExprs[0], ctx.mkInt(1)), (BitVecExpr) ineqExprs[1]);
//            BoolExpr retExpr = ctx.mkAnd(retExpr1, retExpr2);
//            return assignIdToBVFormula(retExpr, ctx, formulas, disjSolver);
//        }
        String id = "fmla_" + formulaCount;
        BoolExpr idBe = getIdsBoolExpr(id, ctx); //for disjoint solver
        formulaCount++;
        be = simplifyMultBy1BVAtomicFormula(be, ctx);
        HashSet<BvVariable> varsFormula = Util.collectBvVars(be, ctx);
        vars = Util.varUnion(vars, varsFormula);
        formulas.put(id, new TransformedFormula(be, 0, varsFormula));
        return idBe;
    }

    public BoolExpr simplifyMultBy1BVAtomicFormula(BoolExpr e, Context ctx) {
        Expr[] exprs = e.getArgs();
        BoolExpr be = null;
        BitVecExpr ae1 = simplifyMultBy1BVExpr((BitVecExpr) exprs[0], ctx);
        BitVecExpr ae2 = simplifyMultBy1BVExpr((BitVecExpr) exprs[1], ctx);
        if (e.isBVUGT()) {
            be = ctx.mkBVUGT(ae1, ae2);
        } else if (e.isBVUGE()) {
            be = ctx.mkBVUGE(ae1, ae2);

        } else if (e.isBVULT()) {
            be = ctx.mkBVULT(ae1, ae2);

        } else if (e.isBVULE()) {
            be = ctx.mkBVULE(ae1, ae2);

        } else if (e.isEq()) {
            be = ctx.mkEq(ae1, ae2);
        }

        return be;
    }

    public BitVecExpr simplifyMultBy1BVExpr(BitVecExpr bvExpr, Context ctx) {
        int bvSize = bvExpr.getSortSize();
        BitVecExpr one = ctx.mkBV(1, bvSize);
        if (bvExpr.isBVMul()) {
            Expr[] multComponents = bvExpr.getArgs();
            if (multComponents.length > 2) {
                return bvExpr;
            }
            BitVecExpr comp0 = (BitVecExpr) multComponents[0];
            BitVecExpr comp1 = (BitVecExpr) multComponents[1];

            if (comp0.equals(one)) {
                return comp1;
            }
            if (comp1.equals(one)) {
                return comp0;
            }
            //none of them is one
            return bvExpr;
        } else { //the expression is not mult, so we cannot simplify mult by 1
            return bvExpr;
        }
    }

    public HashMap<String, TransformedFormula> assignIdToFormula(BoolExpr bExpr, Context ctx, Solver disjSolver) {
        bExpr = (BoolExpr) bExpr;
        ArrayList<Expr> list = new ArrayList<>();
        listConstraints(bExpr, ctx, list);
        Expr[] exprs = list.toArray(new Expr[list.size()]);

        HashMap<String, TransformedFormula> formulas = new HashMap<>();
        boolean isDisjunction = false;
        BoolExpr disjExpr = (BoolExpr) hashFormulas(exprs, ctx, formulas, isDisjunction).simplify();
        //System.out.println("disj expr " + disjExpr);
        disjSolver.add(disjExpr);
        return formulas;
    }

    public BoolExpr hashFormulas(Expr[] exprs, Context ctx, HashMap<String, TransformedFormula> formulas, boolean isDisjunction) {
        BoolExpr be;
        BoolExpr beAnd = ctx.mkTrue();
        for (int i = 0; i < exprs.length; i++) {
            be = (BoolExpr) exprs[i];
            if (be.isOr()) { //single OR nesting considered
                beAnd = ctx.mkAnd(beAnd, hashFormulasSingleList(be.getArgs(), ctx, formulas, true));
            } else {
                beAnd = ctx.mkAnd(beAnd, assignIdToSingleConstraint(be, ctx, formulas));
            }
        }
        return beAnd;
    }

    public BoolExpr hashFormulasSingleList(Expr[] exprs, Context ctx, HashMap<String, TransformedFormula> formulas, boolean isDisjunction) {
        BoolExpr be;
        if (isDisjunction) {
            BoolExpr beOr = ctx.mkFalse();
            for (int i = 0; i < exprs.length; i++) {
                be = (BoolExpr) exprs[i];
                beOr = ctx.mkOr(beOr, assignIdToSingleConstraint(be, ctx, formulas));
            }
            return beOr;
        } else {
            BoolExpr beAnd = ctx.mkTrue();
            for (int i = 0; i < exprs.length; i++) {
                be = (BoolExpr) exprs[i];
                beAnd = ctx.mkAnd(beAnd, assignIdToSingleConstraint(be, ctx, formulas));
            }
            return beAnd;
        }
    }

    public BoolExpr getIdsBoolExpr(String id, Context ctx) {
        BoolExpr idBoolExpr;
        if (idStringToBoolExpr.containsKey(id)) {
            return idStringToBoolExpr.get(id);
        } else {
            idBoolExpr = ctx.mkBoolConst(id);
            idStringToBoolExpr.put(id, idBoolExpr);
            return idBoolExpr;
        }
    }

    public BoolExpr assignIdToSingleConstraint(BoolExpr be, Context ctx, HashMap<String, TransformedFormula> formulas) {
        String id;
        if (be.isNot()) { //assuming negation normal form
            return processNegation(ctx, (BoolExpr) be.getArgs()[0], formulas);
        } else if (be.isLT() || be.isGT()) {
            return convertStrictIneqToNonStrictIneq(ctx, be, formulas);
        } else {
            id = "fmla_" + formulaCount;
            formulaCount++;
            HashSet<BvVariable> varsFormula = Util.collectBvVars(be, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(be, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        }
    }

    public BoolExpr processNegation(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] exprs = be.getArgs();
        ArithExpr a0 = (ArithExpr) exprs[0];
        ArithExpr a1 = (ArithExpr) exprs[1];
        HashSet<BvVariable> varsFormula;
        BoolExpr retExpr;
        String id;
        if (be.isLE()) {
            retExpr = ctx.mkGt(a0, a1);
            return convertStrictIneqToNonStrictIneq(ctx, retExpr, formulas);
        } else if (be.isLT()) {
            retExpr = ctx.mkGe(a0, a1);
            id = "fmla_" + formulaCount;
            formulaCount++;
            varsFormula = Util.collectBvVars(retExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(retExpr, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        } else if (be.isGE()) {
            retExpr = ctx.mkLt(a0, a1);
            return convertStrictIneqToNonStrictIneq(ctx, retExpr, formulas);
        } else if (be.isGT()) {
            retExpr = ctx.mkLe(a0, a1);
            id = "fmla_" + formulaCount;
            formulaCount++;
            varsFormula = Util.collectBvVars(retExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(retExpr, 0, varsFormula));
            return getIdsBoolExpr(id, ctx);
        } else {
            //equality could come in
            System.err.println("is a disjunction (not " + be + ")/n not is NNF");
            System.exit(1);
            return null;
        }

    }

    public void listConstraints(BoolExpr bExpr, Context ctx, ArrayList<Expr> exprList) {
        Expr[] exprs1;
        //  ArrayList<Expr> exprList = new ArrayList<>();
        //BoolExpr acc = ctx.mkTrue();
//        System.out.println("bExpr "+bExpr);
        if (!bExpr.isTrue()) {
            if (bExpr.isAnd()) {
                //check if there is a nested and
                exprs1 = bExpr.getArgs();
//            System.out.println("length "+exprs1.length);
                for (int i = 0; i < exprs1.length; i++) {
//                System.out.println("calling collect constraints");
                    listConstraints((BoolExpr) exprs1[i], ctx, exprList);
                }
            } else {
                exprList.add(bExpr);
            }
        }

    }

    /*
     simplify exprssions in each side of the inequalities
     */
    public BoolExpr simplifyArithFormula(Context ctx, BoolExpr be) {
        Expr[] exprs = be.getArgs();
        ArithExpr ae0 = (ArithExpr) exprs[0].simplify();
        ArithExpr ae1 = (ArithExpr) exprs[1].simplify();
        if (be.isLE()) {
            return ctx.mkLe(ae0, ae1);
        }
        if (be.isLT()) {
            return ctx.mkLt(ae0, ae1);
        }
        if (be.isEq()) {
            return ctx.mkEq(ae0, ae1);
        }
        if (be.isGE()) {
            return ctx.mkGe(ae0, ae1);
        }
        if (be.isGT()) {
            return ctx.mkGt(ae0, ae1);
        }
        return null;
    }

    public void processEqualities(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] eqExprs;
        HashSet<BvVariable> varsFormula;
        BoolExpr normalizedExpr;
        String id;
        eqExprs = be.getArgs();

        id = "fmla_" + formulaCount;
        formulaCount++;
        varsFormula = Util.collectBvVars(be, ctx);
        vars = Util.varUnion(vars, varsFormula);

        normalizedExpr = ctx.mkGe((ArithExpr) eqExprs[0], (ArithExpr) eqExprs[1]);
        formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));

        id = "fmla_" + formulaCount;
        formulaCount++;
        normalizedExpr = ctx.mkLe((ArithExpr) eqExprs[0], (ArithExpr) eqExprs[1]);
        formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
    }

    /*
     This convertion holds only for modular arithmetic
     */
    public BoolExpr convertStrictIneqToNonStrictIneq(Context ctx, BoolExpr be, HashMap<String, TransformedFormula> formulas) {
        Expr[] ineqExprs;
        HashSet<BvVariable> varsFormula;
        BoolExpr normalizedExpr;
        String id;
        BoolExpr id1, id2;
        ineqExprs = be.getArgs();
        if (be.isLT()) {
            id = "fmla_" + formulaCount;
            id1 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            normalizedExpr = ctx.mkGe((ArithExpr) ineqExprs[1], ctx.mkInt(Util.min_neg() + 1));
            varsFormula = Util.collectBvVars(normalizedExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));

            id = "fmla_" + formulaCount;
            id2 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            ArithExpr secondExpr = ctx.mkSub((ArithExpr) ineqExprs[1], ctx.mkInt(1));
            normalizedExpr = ctx.mkLe((ArithExpr) ineqExprs[0], secondExpr);
            varsFormula = Util.collectBvVars(normalizedExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            return ctx.mkAnd(id1, id2);
        } else if (be.isGT()) {
            id = "fmla_" + formulaCount;
            id1 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            normalizedExpr = ctx.mkGe((ArithExpr) ineqExprs[0], ctx.mkInt(Util.min_neg() + 1));
            varsFormula = Util.collectBvVars(normalizedExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            id = "fmla_" + formulaCount;
            id2 = getIdsBoolExpr(id, ctx);
            formulaCount++;
            ArithExpr firstExpr = ctx.mkSub((ArithExpr) ineqExprs[0], ctx.mkInt(1));
            normalizedExpr = ctx.mkGe(firstExpr, (ArithExpr) ineqExprs[1]);
            varsFormula = Util.collectBvVars(normalizedExpr, ctx);
            vars = Util.varUnion(vars, varsFormula);
            formulas.put(id, new TransformedFormula(normalizedExpr, 0, varsFormula));
            return ctx.mkAnd(id1, id2);
        } else {
            return null;
        }
    }

    public boolean allTransformed() {
        for (String b : transformedFormulasA.keySet()) {
            if (transformedFormulasA.get(b).getStatus() == 0) {
                return false;
            }
        }
        return true;
    }

    public BoolExpr computeMAInterpolant(String file) {
        BoolExpr interpolant = null;
        try {
            initialize();
            long beingTime = System.nanoTime();
            interpolant = interpolantMAFromFile(file);
            System.out.println("interpolant formula: " + interpolant);
            long endTime = System.nanoTime();
            long time = endTime - beingTime;
            System.out.println(Message.showQEStatistics(file, time / 1000000, transformedFormulasA.size() + transformedFormulasB.size(), refinementCount, nrConstraintRelaxed));
            dispose();

        } catch (Exception e) {
            e.printStackTrace();
        }
        return interpolant;
    }

    HashSet<BvVariable> convertIntVarsToBvVars(HashSet<IntExpr> intVars, Context ctx) {
        HashSet<BvVariable> bvVars = new HashSet<>();
        BvVariable bvVar;
        int size;
        for (IntExpr ie : intVars) {
            size = sizeIntVar.get(ie);
            bvVar = new BvVariable(ctx.mkSymbol(ie.toString()), size);
            bvVars.add(bvVar);
        }
        return bvVars;
    }

    void printCoreConstrants(String[] unsatcore, Context ctx, Model deltaModel) {
        TransformedFormula tf;
        ArrayList<ArithFormula> af;
        GRBConstr c;
        String[] unsatcoreO = mapUnsatCoreIdsToOriginal(ctx, unsatcore);
        for (int i = 0; i < unsatcoreO.length; i++) {
            tf = transformedFormulasA.get(unsatcoreO[i]);
            System.out.println(" id: " + unsatcoreO[i]);
            af = tf.getFormula();
            for (int j = 0; j < af.size(); j++) {
                System.out.println("constr orig " + j + " " + af.get(j).getFormula());
                System.out.println("constr " + j + " " + Z3Interface.evalExprInModelWoMc(deltaModel, af.get(j).getFormula()));
            }
        }
    }

    void printIdentifiedFormulas() {
        TransformedFormula tf;
        for (String i : transformedFormulasA.keySet()) {
            tf = transformedFormulasA.get(i);
            // System.out.println("id: " + i + " " + tf.getOriginalFormula());
        }
    }

    public void printAssertion(Solver s) {
        BoolExpr[] ass = s.getAssertions();
        for (int i = 0; i < ass.length; i++) {
            System.out.println(" assertion " + i + " " + ass[i]);
        }
    }

    public void printAssumption(String[] ass) {
        for (int i = 0; i < ass.length; i++) {
            System.out.println(" assumption " + i + " " + ass[i]);
        }
    }

}
