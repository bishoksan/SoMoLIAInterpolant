/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.ApplyResult;
import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.Context;
import com.microsoft.z3.Expr;
import com.microsoft.z3.FuncDecl;
import com.microsoft.z3.Goal;
import com.microsoft.z3.IntExpr;
import com.microsoft.z3.InterpolationContext;
import com.microsoft.z3.InterpolationContext.ComputeInterpolantResult;
import com.microsoft.z3.Model;
import com.microsoft.z3.Optimize;
import com.microsoft.z3.Params;
import com.microsoft.z3.Solver;
import com.microsoft.z3.Status;
import com.microsoft.z3.Tactic;
import gurobi.GRBException;
import gurobi.GRBModel;
import gurobi.GRBVar;
import java.io.File;
import java.util.ArrayList;
import java.util.HashMap;

/**
 *
 * @author kafle
 */
public class Z3Interface {

    public Context getContext() {
        HashMap<String, String> cfg = new HashMap<>();
//        cfg.put(":pp-min-alias-size", "1000000");
//        cfg.put(":pp-max-depth", "1000000");
        //cfg.put("proof", "true");
        //cfg.put("auto-config", "false");
        //cfg.put("enable_simplex", "true");
        //(set-option :smt.pb.enable_simplex true)
        //return new Context(cfg);
        //cfg.put("ELIM_QUANTIFIERS", "true");
        Context ctx = new Context(cfg);

        //http://stackoverflow.com/questions/13463153/prevent-solution-from-being-simplified
        //the two line that follows will ask z3 not to produce let expressions as a pretty printing
//        Params p= ctx.mkParams();
//        p.add(":pp-min-alias-size", "1000000");
//        p.add(":pp-max-depth", "1000000");
        return ctx;
    }

    public InterpolationContext getInerpolationContext() {
        HashMap<String, String> cfg = new HashMap<String, String>();
        cfg.put("proof", "true");
        cfg.put("model", "true");
        cfg.put("smtlib2_compliant", "true");
        cfg.put("unsat_core", "true");
        //cfg.put("produce-interpolants", "true");
        return InterpolationContext.mkContext(cfg);
    }

    public BoolExpr readSMTInput(String inputFile, Context context) {
        if (inputFile.endsWith(".smt2")) {
            return readSMTLIB2File(inputFile, context);
        } else {
            return readSMTLIB1File(inputFile, context);
        }
    }

    public BoolExpr readSMTInputWSymbols(String inputFile, FuncDecl[] fds, InterpolationContext context) {
        if (inputFile.endsWith(".smt2")) {
            return readSMTLIB2FileWSymbols(inputFile, fds, context);
        } else {
            return readSMTLIB1File(inputFile, context);
        }
    }

    /**
     * read input in SMT-LIB2 format from the input
     *
     * @param file
     * @param ctx
     * @return
     */
    public BoolExpr readSMTLIB2File(String file, Context ctx) {
        BoolExpr smtFormulas = null;
        File f = new File(file);
        try {
            if (f.exists()) {
                smtFormulas = ctx.parseSMTLIB2File(file, null, null, null, null);
            } else {
                System.out.println("Error: the input file " + file + " does not exist");
                System.exit(1);
            }
        } catch (Exception e) {
            // e.printStackTrace();
            e.printStackTrace();
            System.out.println("parsing error  " + e.getLocalizedMessage());
        }
        return smtFormulas;
    }
    
        //assuming bExpr to be a conjunction, the last being (get-interpolant formulaA formulaB) and no further assertions after that
    Expr[] getFormulasAandB(BoolExpr bExpr) {
        Expr[] exprs = bExpr.getArgs();
        int len = exprs.length;
        //the last element should be (get-interpolant formulaA formulaB)
        Expr interpolantConjunct = exprs[len - 1];
        //System.out.println("interpolant part " + interpolantConjunct);
        Expr[] interpolantParts = interpolantConjunct.getArgs();
        return interpolantParts;
    }

    public BoolExpr readSMTLIB2FileWSymbols(String file, FuncDecl[] fds, InterpolationContext ctx) {
        BoolExpr smtFormulas = null;
        File f = new File(file);
        try {
            if (f.exists()) {
                smtFormulas = ctx.parseSMTLIB2File(file, null, null, null, fds);
            } else {
                System.out.println("Error: the input file " + file + " does not exist");
                System.exit(1);
            }
        } catch (Exception e) {
            // e.printStackTrace();
            e.printStackTrace();
            System.out.println(e.getCause());
            System.out.println("parsing error  " + e.getLocalizedMessage());
        }
        return smtFormulas;
    }

    public BoolExpr readSMTLIB2FileWDecl(String file, Context ctx) {
        BoolExpr smtFormulas = null;
        File f = new File(file);
        try {
            if (f.exists()) {
                smtFormulas = ctx.parseSMTLIB2File(file, null, null, null, null);
            } else {
                System.out.println("Error: the input file " + file + " does not exist");
                System.exit(1);
            }
        } catch (Exception e) {
            // e.printStackTrace();
            e.printStackTrace();
            System.out.println("parsing error  " + e.getLocalizedMessage());
        }
        return smtFormulas;
    }

    public BoolExpr readSMTLIB1File(String file, Context ctx) {
        BoolExpr smtFormulas = null;
        File f = new File(file);
        try {
            if (f.exists()) {
                ctx.parseSMTLIBFile(file, null, null, null, null);
                return ctx.getSMTLIBFormulas()[0];
                //return ctx.mkAnd(ctx.getSMTLIBFormulas());
            } else {
                System.out.println("Error: the input file " + file + " does not exist");
                System.exit(1);
            }
        } catch (Exception e) {
            // e.printStackTrace();
            e.printStackTrace();
            System.out.println("parsing error " + e.getMessage());
            System.exit(1);
        }
        return smtFormulas;
    }

    public Solver createMinimalModelProdSolver(Context ctx) {
//        Solver solver = ctx.mkSolver(ctx.mkSymbol("QF_BF")); //"QF_LIA" logic for LIA
        Solver solver = ctx.mkSolver(); //"QF_LIA" logic for LIA
        Params p = ctx.mkParams();
        p.add("auto_config", false);
        p.add("relevancy", 2); //these 2 parameters produces minimal model(http://stackoverflow.com/questions/16291066/how-do-i-get-z3-to-return-minimal-model)
        solver.setParameters(p);
        return solver;
    }

    public Solver createLIASolver(Context ctx) {
//        Solver solver = ctx.mkSolver(ctx.mkSymbol("QF_BF")); //"QF_LIA" logic for LIA
        Solver solver = ctx.mkSolver(ctx.mkSymbol("QF_LIA")); //"QF_LIA" logic for LIA
//        Params p = ctx.mkParams();
//        p.add("solver2_timeout", 0); //turning off incremental solving, time in millisecond
//        solver.setParameters(p);
        return solver;
    }

    public Model getModel(Solver solver) {
        return solver.getModel();
    }

    /**
     * only handles integer expressions
     */
    public BoolExpr getZ3ModelAsAssertions(Context ctx, Model m) {
        BoolExpr be = ctx.mkTrue();
        BoolExpr modelExpr;
        FuncDecl[] fdcls = m.getConstDecls();
        for (int i = 0; i < fdcls.length; i++) {
            if (!fdcls[i].getRange().toString().equals("Bool")) { //ignoring bool sort, they are put through assertions
                modelExpr = ctx.mkEq(ctx.mkApp(fdcls[i]), m.getConstInterp(fdcls[i]));
                be = ctx.mkAnd(be, modelExpr);
            }
        }
        return be;
    }

    public BoolExpr[] getUnsatCore(Solver solver) {
        return solver.getUnsatCore();
    }

    public Status checkFormula(Solver solver, BoolExpr[] assumptions) {
        return solver.check(assumptions);
    }

    public Status checkFormula(Solver solver) {
        return solver.check();
    }

    public Status checkFormula(Optimize opt) {
        return opt.Check();
    }

    public Optimize createOptimizer(Context ctx) {
        return ctx.mkOptimize();
    }

    public void resetSolver(Solver solver) {
        solver.reset();
    }

    /**
     * evaluates an expression in a model
     */
    public static Expr evalExprInModel(Model model, Expr expr) {
        return model.evaluate(expr, true); // the second parameter says model_completion=True
    }

    /**
     * evaluates an expression in a model
     */
    public static Expr evalExprInModelWoMc(Model model, Expr expr) {
        return model.evaluate(expr, false); // the second parameter says model_completion=True
    }

    //(apply (then simplify propagate-values (par-then split-clause propagate-ineqs)))
    //(apply (then simplify propagate-values (par-then (repeat (or-else split-clause skip)) propagate-ineqs)))
    public BoolExpr simplifyExpr(Context ctx, BoolExpr e) {
        Goal g = ctx.mkGoal(false, false, false);//maGoal(model, unsacore, proofs)
//        System.out.println("orig " + e);
        BoolExpr be = ctx.mkFalse();
        g.add(e);
        Tactic t1 = ctx.mkTactic("simplify");
        Tactic t2 = ctx.mkTactic("propagate-values");
        Tactic t3 = ctx.mkTactic("split-clause");
//        Tactic preamble=ctx.then(ctx.mkTactic("simplify"),
//                ctx.mkTactic("propagate-values"), 
//                ctx.mkTactic("ctx-simplify"), 
//                ctx.mkTactic("lift-if"), 
//                ctx.mkTactic("gaussian"), 
//                ctx.mkTactic("simplify"));
        //Tactic t4 = ctx.mkTactic("propagate-ineqs");
        //Tactic t5 = ctx.mkTactic("solve-eqs");
//        Tactic t = ctx.then(t1, t2, ctx.parAndThen(t3, t4));
        //Tactic t = ctx.then( t1, t2, ctx.parAndThen(ctx.repeat(ctx.orElse(t3, ctx.skip()),1), t2));//working or
        Tactic t = ctx.then(t1, ctx.repeat(ctx.orElse(t3, ctx.skip()), 1), t2);//also working
        ApplyResult ar = t.apply(g);
        Goal[] g1 = ar.getSubgoals();
        if (g1.length == 1) {

            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        if (g1.length > 1) {
            be = g1[0].AsBoolExpr();
        }
        for (int i = 1; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());
        }
//        System.out.println("simplied " + be);
        g = null;
        g1 = null;
        return be;
    }

    public BoolExpr propagateDelta(Context ctx, BoolExpr e) {
        // BoolExpr be = ctx.mkTrue();
        Goal g = ctx.mkGoal(false, false, false);//mkGoal(model, unsatcore, proofs)
        g.add(e);
        //(apply (then simplify propagate-values split-clause propagate-ineqs))
        Tactic t1 = ctx.mkTactic("simplify");
//        Tactic t2 = ctx.mkTactic("propagate-values");
//        Tactic t4 = ctx.mkTactic("propagate-ineqs");
//        Tactic t3 = ctx.mkTactic("split-clause");
        Tactic t5 = ctx.mkTactic("solve-eqs");
        Tactic t = ctx.then(t5, t1);
        //Goal[] g1= t.apply(g).getSubgoals();
        BoolExpr retExpr = t.apply(g).getSubgoals()[0].AsBoolExpr();
//        for (int i = 0; i < g1.length; i++) {
//            be = ctx.mkAnd(be, g1[i].AsBoolExpr());
//        }
        // System.out.println("actual transfer "+be);
        g = null;
        return retExpr;
    }

    public BoolExpr simplifyQFLIAFormula(Context ctx, BoolExpr f) {
        Goal g = ctx.mkGoal(false, false, false);//maGoal(model, unsatcore, proofs)
        BoolExpr be = ctx.mkFalse();
        g.add(f);
//        System.out.println("received formula "+f);
        Tactic preamble = ctx.then(ctx.mkTactic("simplify"), ctx.mkTactic("propagate-values"),
                ctx.mkTactic("solve-eqs"),
                ctx.mkTactic("simplify"));
//        Tactic  preamble = ctx.mkTactic("simplify");
        ApplyResult ar = preamble.apply(g);
        Goal[] g1 = ar.getSubgoals();
        if (g1.length == 1) {

            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        if (g1.length > 1) {
            be = g1[0].AsBoolExpr();
        }
        for (int i = 1; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());
        }
//        System.out.println("obtained formula "+be);
        g = null;
        g1 = null;
        return be;
    }
//    public BoolExpr simplifyLAFormula(Context ctx, BoolExpr f) {
//        Goal g = ctx.mkGoal(false, false, false);//maGoal(model, unsatcore, proofs)
//        BoolExpr be = ctx.mkFalse();
//        g.add(f);
//        Tactic preamble, mf, pb, bounded, z3QF_LIASMTComp13;
//        preamble=ctx.then(ctx.mkTactic("simplify"),ctx.mkTactic("propagate-values"), 
//                ctx.mkTactic("ctx-simplify"), ctx.mkTactic("lift-if"), ctx.mkTactic("gaussian"), 
//                ctx.mkTactic("simplify"));
//        mf=ctx.then(ctx.failIf(ctx.not(ctx.ilp)), ctx.mkTactic("propagate-bounds"),
//                ctx.orElse(ctx.tryFor(ctx.mkTactic("mip", 5000),
//                        bounded))
//        z3QF_LIASMTComp13= ctx.then(preamble, ctx.orElse(mf, pb, bounded, smt));
//        Tactic t = ctx.then(t1, ctx.repeat(ctx.orElse(t3, ctx.skip()), 1), t2);//also working
//        ApplyResult ar = t.apply(g);
//        Goal[] g1 = ar.getSubgoals();
//        for (int i = 0; i < g1.length; i++) {
//            be = ctx.mkOr(be, g1[i].AsBoolExpr());
//        }
////        System.out.println("simplied " + be);
//        g = null;
//        g1 = null;
//        return be;
//    }

    public BoolExpr getNNF(Context ctx, BoolExpr e) {
        Tactic t = ctx.mkTactic("nnf");
        Goal g = ctx.mkGoal(false, false, false);//maGoal(model, unsacore, proofs)
//        System.out.println("orig " + e);
        BoolExpr be = ctx.mkFalse();
        g.add(e);

        ApplyResult ar = t.apply(g);
        Goal[] g1 = ar.getSubgoals();
        if (g1.length == 1) {
            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        if (g1.length > 1) {
            be = g1[0].AsBoolExpr();
        }
        for (int i = 1; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());
        }
//        System.out.println("simplied " + be);
        g = null;
        g1 = null;
        return be;
    }

    /**
     * write any arithmetic expr in E=<const or E=const form
     */
    public static BoolExpr standariseArithInEq(BoolExpr be, Context ctx) {
        Params p = ctx.mkParams();
        p.add(":arith-lhs", true);
        //this returns, =,  >= or =< possibly preceded by not, but the rhs will only contain constants
        BoolExpr simplifiedExpr = (BoolExpr) be.simplify(p);
        if (simplifiedExpr.isNot()) {
            BoolExpr arithExpr = (BoolExpr) simplifiedExpr.getArgs()[0];
            if (arithExpr.isLE()) {
                Expr[] exprs = arithExpr.getArgs();
                ArithExpr ae = ctx.mkSub(ctx.mkUnaryMinus((ArithExpr) exprs[1]), ctx.mkInt(1));
                return ctx.mkLe((ArithExpr) ctx.mkUnaryMinus((ArithExpr) exprs[0]).simplify(), (ArithExpr) ae.simplify());
            }
            //is greaterequal
            Expr[] exprs = arithExpr.getArgs();
            ArithExpr ae = ctx.mkSub((ArithExpr) exprs[1], ctx.mkInt(1));
            return ctx.mkLe((ArithExpr) exprs[0], (ArithExpr) ae.simplify());
        }
        //not preceded by "not"
        if (simplifiedExpr.isGE()) {
            Expr[] exprs = simplifiedExpr.getArgs();
            return ctx.mkLe((ArithExpr) ctx.mkUnaryMinus((ArithExpr) exprs[0]).simplify(), (IntExpr) ctx.mkUnaryMinus((IntExpr) exprs[1].simplify()));
        }
        //equal case
        if (simplifiedExpr.isEq()) {
            Expr[] exprs = simplifiedExpr.getArgs();
            return ctx.mkEq((ArithExpr) exprs[0], (ArithExpr) exprs[1]);
        }
        //the last case is in standard form or equality
        return be;
    }

    /**
     * write any arithmetic expr in E=<const form
     */
    public ArrayList<BoolExpr> standariseBoolExpr(BoolExpr be, Context ctx) {
        ArrayList<BoolExpr> standarisedExpr = new ArrayList<>();
        Params p = ctx.mkParams();
        p.add(":arith-lhs", true);
        //this returns >= or =< possibly preceded by not, but the rhs will only contain constants
        BoolExpr simplifiedExpr = (BoolExpr) be.simplify(p);
        if (simplifiedExpr.isNot()) {
            BoolExpr arithExpr = (BoolExpr) simplifiedExpr.getArgs()[0];
            if (arithExpr.isLE()) {
                Expr[] exprs = arithExpr.getArgs();
                ArithExpr ae = ctx.mkSub(ctx.mkUnaryMinus((ArithExpr) exprs[1]), ctx.mkInt(1));
                standarisedExpr.add(ctx.mkLe((ArithExpr) ctx.mkUnaryMinus((ArithExpr) exprs[0]).simplify(), (ArithExpr) ae.simplify()));
                return standarisedExpr;
            }
            //is greaterequal
            Expr[] exprs = arithExpr.getArgs();
            ArithExpr ae = ctx.mkSub((ArithExpr) exprs[1], ctx.mkInt(1));
            standarisedExpr.add(ctx.mkLe((ArithExpr) exprs[0], (ArithExpr) ae.simplify()));
            return standarisedExpr;
        }
        //not preceded by "not"
        if (simplifiedExpr.isGE()) {
            Expr[] exprs = simplifiedExpr.getArgs();
            standarisedExpr.add(ctx.mkLe((ArithExpr) ctx.mkUnaryMinus((ArithExpr) exprs[0]).simplify(), (IntExpr) ctx.mkUnaryMinus((IntExpr) exprs[1].simplify())));
            return standarisedExpr;
        }
        //equal case
        if (simplifiedExpr.isEq()) {
            Expr[] exprs = simplifiedExpr.getArgs();
            standarisedExpr.add(ctx.mkLe((ArithExpr) exprs[0], (ArithExpr) exprs[1]));
            standarisedExpr.add(ctx.mkLe((ArithExpr) ctx.mkUnaryMinus((ArithExpr) exprs[0]).simplify(), (IntExpr) ctx.mkUnaryMinus((IntExpr) exprs[1].simplify())));
            return standarisedExpr;
        }
        //the last case is in standard form
        standarisedExpr.add(simplifiedExpr);
        return standarisedExpr;
    }

    public OptDeltaValues getMaxMinDelta(IntExpr delta, BoolExpr be) {
        Expr[] exprs = be.getArgs();
        OptDeltaValues deltaOpt = new OptDeltaValues(delta);
        int count = 0;
        for (Expr e : exprs) {
            BoolExpr e1 = (BoolExpr) e;
            if (e1.isGE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    IntExpr min = (IntExpr) e1.getArgs()[1];
                    // System.out.println("write min " + min);
                    deltaOpt.setMin(min);
                }
            } else if (e1.isLE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    IntExpr max = (IntExpr) e1.getArgs()[1];
                    // System.out.println("write max " + max);
                    deltaOpt.setMax(max);
                }
            }
            if (count == 2) {
                return deltaOpt;
            }
        }
        return deltaOpt;
    }

    public BoolExpr getMaxMinDeltaExpr(GRBModel grbModel, Context ctx, IntExpr delta, BoolExpr be, HashMap<IntExpr, GRBVar> z3GRBVarMap) {
//        if (be.isFalse()) {
//            return ctx.mkEq(delta, ctx.mkInt(0));
//        }
        GRBVar grbDeltaVar;
        double min = 0, max = 0;
        Expr[] exprs;
        if (be.isAnd()) {
            exprs = be.getArgs();
        } else {
            exprs = new Expr[1];
            exprs[0] = be;
        }

        BoolExpr retExpr = ctx.mkTrue();

        int count = 0;
        for (Expr e : exprs) {
            BoolExpr e1 = (BoolExpr) e;
            if (e1.isEq()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) { //if it is equality then it is obvious max and min
                    min = Double.parseDouble(aexprs[1].toString());
                    grbDeltaVar = Util.createGRBVar(grbModel, delta, min, min);
                    z3GRBVarMap.put(delta, grbDeltaVar);
                    updateModel(grbModel);
                    return e1;
                }
            }
            if (e1.isGE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    retExpr = ctx.mkAnd(retExpr, e1);
                    min = Double.parseDouble(aexprs[1].toString());
                }
            } else if (e1.isLE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    retExpr = ctx.mkAnd(retExpr, e1);
                    max = Double.parseDouble(aexprs[1].toString());
                }
            }
            if (count == 2) { //both min and max computed already
                grbDeltaVar = Util.createGRBVar(grbModel, delta, min, max);
                z3GRBVarMap.put(delta, grbDeltaVar);
                updateModel(grbModel);
                return retExpr;
            }
        }
        return retExpr;
    }

    public BoolExpr getMaxMinDeltaExpr(Context ctx, IntExpr delta, BoolExpr be) {
//        if (be.isFalse()) {
//            return ctx.mkEq(delta, ctx.mkInt(0));
//        }
        double min = 0, max = 0;
        Expr[] exprs;
        if (be.isAnd()) {
            exprs = be.getArgs();
        } else {
            exprs = new Expr[1];
            exprs[0] = be;
        }

        BoolExpr retExpr = ctx.mkTrue();

        int count = 0;
        for (Expr e : exprs) {
            BoolExpr e1 = (BoolExpr) e;
            if (e1.isEq()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) { //if it is equality then it is obvious max and min
                    min = Double.parseDouble(aexprs[1].toString());
                    return e1;
                }
            }
            if (e1.isGE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    retExpr = ctx.mkAnd(retExpr, e1);
                    min = Double.parseDouble(aexprs[1].toString());
                }
            } else if (e1.isLE()) {
                Expr[] aexprs = e1.getArgs();
                IntExpr ie1 = (IntExpr) aexprs[0];
                if (ie1.equals(delta)) {
                    count++;
                    retExpr = ctx.mkAnd(retExpr, e1);
                    max = Double.parseDouble(aexprs[1].toString());
                }
            }
            if (count == 2) { //both min and max computed already
                return retExpr;
            }
        }
        return retExpr;
    }

    public GRBModel updateModel(GRBModel model) {
        try {
            model.update();
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return model;
    }

    /*for some unknown reason it sometimes returns false even though it should not be the case*/
    public BoolExpr inferDeltaBoundsfromAExpr(Context ctx, BoolExpr be) {
        Tactic t1 = ctx.mkTactic("simplify");
        Tactic t2 = ctx.mkTactic("propagate-ineqs");
        Tactic t = ctx.then(t2, t1);
        Goal g = ctx.mkGoal(false, false, false);
        g.add(be);
//        System.out.println("formula before "+be);
        BoolExpr result = t.apply(g).getSubgoals()[0].AsBoolExpr();
//        System.out.println("results of the expr " + result);
        return result;
    }

    public BoolExpr preProcessQBVFormulasForQE(Context ctx, BoolExpr beInput) {

        Params solveEqP = ctx.mkParams();
        solveEqP.add("solve_eqs_max_occs", 2);
        Params simp2P = ctx.mkParams();
        simp2P.add("som", true);
        simp2P.add("pull_cheap_ite", true);
        simp2P.add("push_ite_bv", false);
        simp2P.add("local_ctx", true);
        simp2P.add("local_ctx_limit", 10000000);
        simp2P.add("flat", true);
        simp2P.add("hoist_mul", false); // required by som
        Params hoistP = ctx.mkParams();
        hoistP.add("hoist_mul", true);
        hoistP.add("som", false);
        Tactic t = ctx.mkTactic("qfbv");
        Tactic simplify = ctx.mkTactic("simplify");
        Tactic propagateValues = ctx.mkTactic("propagate-values");
        Tactic maxBvSharing = ctx.mkTactic("max-bv-sharing");
        Tactic solveEqs = ctx.mkTactic("solve-eqs");
        Tactic elimUncnstr = ctx.mkTactic("elim-uncnstr");
        Tactic ctxSimplify = ctx.mkTactic("ctx-simplify");
        Params ctxSimplifyP = ctx.mkParams();
        ctxSimplifyP.add("max_depth", 30);
        ctxSimplifyP.add("max_steps", 5000000);

        Params pullIteP = ctx.mkParams();
        pullIteP.add("pull_cheap_ite", true);
        pullIteP.add("local_ctx", true);
        pullIteP.add("local_ctx_limit", 10000000);

        //taken from quant_tactics.cpp of z3
        Tactic preamble = ctx.andThen(
                simplify,
                propagateValues,
                ctx.usingParams(ctxSimplify, ctxSimplifyP),
                ctx.usingParams(simplify, pullIteP),
                solveEqs,
                //elimUncnstr,
                simplify
        );
        BoolExpr be = ctx.mkFalse();
        Goal g = ctx.mkGoal(false, false, false);
        g.add(beInput);
        ApplyResult ar = preamble.apply(g);

        Goal[] g1 = ar.getSubgoals();
        //System.out.println("length " + g1.length);
        if (g1.length == 1) {
            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        System.err.println("length greater than 1: tactic preProcessQBVFormulasForQE");
        System.exit(1);
        for (int i = 0; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());
        }
        g = null;
        g1 = null;
        return (BoolExpr) be.simplify();
    }

    public BoolExpr preProcessQFBVFormulasForQE(Context ctx, BoolExpr beInput) {
        Params solveEqP = ctx.mkParams();
        solveEqP.add("solve_eqs_max_occs", 2);
        Params simp2P = ctx.mkParams();
        simp2P.add("som", true);
        simp2P.add("pull_cheap_ite", true);
        simp2P.add("push_ite_bv", false);
        simp2P.add("local_ctx", true);
        simp2P.add("local_ctx_limit", 10000000);
        simp2P.add("flat", true);
        simp2P.add("hoist_mul", false); // required by som
        Params hoistP = ctx.mkParams();
        hoistP.add("hoist_mul", true);
        hoistP.add("som", false);
        Tactic simplify = ctx.mkTactic("simplify");
        Tactic propagateValues = ctx.mkTactic("propagate-values");
        Tactic maxBvSharing = ctx.mkTactic("max-bv-sharing");
        Tactic solveEqs = ctx.mkTactic("solve-eqs");
        //Tactic elimUncnstr = ctx.mkTactic("elim-uncnstr");

        Tactic preamble = ctx.andThen(
                simplify,
                propagateValues,
                ctx.usingParams(solveEqs, solveEqP),
                //elimUncnstr,
                ctx.usingParams(simplify, simp2P),
                ctx.usingParams(simplify, hoistP),
                maxBvSharing);
        BoolExpr be = ctx.mkFalse();
        Goal g = ctx.mkGoal(false, false, false);
        g.add(beInput);
        ApplyResult ar = preamble.apply(g);

        Goal[] g1 = ar.getSubgoals();
        //System.out.println("length " + g1.length);
        if (g1.length == 1) {

            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        System.err.println("length greater than 1: tactic preProcessQFBVFormulasForQE");
        System.exit(1);
        for (int i = 0; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());

        }
        return (BoolExpr) be.simplify();
    }

    public BoolExpr preProcessQFBVFormulas(Context ctx, BoolExpr beInput) {
        Params solveEqP = ctx.mkParams();
        solveEqP.add("solve_eqs_max_occs", 2);
        Params simp2P = ctx.mkParams();
        simp2P.add("som", true);
        simp2P.add("pull_cheap_ite", true);
        simp2P.add("push_ite_bv", false);
        simp2P.add("local_ctx", true);
        simp2P.add("local_ctx_limit", 10000000);
        simp2P.add("flat", true);
        simp2P.add("hoist_mul", false); // required by som
        Params hoistP = ctx.mkParams();
        hoistP.add("hoist_mul", true);
        hoistP.add("som", false);
//
        // used in z3
//        return and_then(
//                mk_simplify_tactic(m),
//                mk_propagate_values_tactic(m),
//                using_params(mk_solve_eqs_tactic(m), solve_eq_p),
//                mk_elim_uncnstr_tactic(m),
//                if_no_proofs(if_no_unsat_cores(mk_bv_size_reduction_tactic(m))),
//                using_params(mk_simplify_tactic(m), simp2_p),
//                using_params(mk_simplify_tactic(m), hoist_p),
//                mk_max_bv_sharing_tactic(m),
//                if_no_proofs(if_no_unsat_cores(mk_ackermannize_bv_tactic(m, p)))
//        );

        //Tactic t = ctx.mkTactic("qfbv");
        Tactic simplify = ctx.mkTactic("simplify");
        Tactic propagateValues = ctx.mkTactic("propagate-values");
        Tactic maxBvSharing = ctx.mkTactic("max-bv-sharing");
        Tactic solveEqs = ctx.mkTactic("solve-eqs");
        Tactic elimUncnstr = ctx.mkTactic("elim-uncnstr");

        Tactic preamble = ctx.andThen(
                simplify,
                propagateValues,
                //ctx.usingParams(solveEqs, solveEqP), //this shows some prob., maybe does not return equiv solution
                //elimUncnstr,
                ctx.usingParams(simplify, simp2P),
                ctx.usingParams(simplify, hoistP),
                maxBvSharing);
        BoolExpr be = ctx.mkFalse();
        Goal g = ctx.mkGoal(false, false, false);
        g.add(beInput);
        ApplyResult ar = preamble.apply(g);

        Goal[] g1 = ar.getSubgoals();
        //System.out.println("length " + g1.length);
        if (g1.length == 1) {
            be = g1[0].AsBoolExpr();
            g = null;
            g1 = null;
            return be;
        }
        System.err.println("length greater than 1: tactic preProcessQFBVFormulas");
        System.exit(1);
        for (int i = 0; i < g1.length; i++) {
            be = ctx.mkOr(be, g1[i].AsBoolExpr());

        }

        return (BoolExpr) be.simplify();
    }

    public void solveBVTactic(BoolExpr be, Context ctx) {
        BoolExpr ret;
        Tactic t = ctx.mkTactic("qfbv");
        Goal g = ctx.mkGoal(false, false, false);
        g.add(be);
        ret = t.apply(g).getSubgoals()[0].AsBoolExpr();
        System.out.println("ret " + ret);
    }

    public BoolExpr eliminateQuantifiers(Context ctx, BoolExpr be) {
//            System.out.println("formula "+be);
        Tactic t = ctx.mkTactic("qe");
        Goal g = ctx.mkGoal(false, false, false);
        g.add(be);
        BoolExpr qfFormula = ctx.mkFalse();
        Goal[] results = t.apply(g).getSubgoals();
        int resLength = results.length;
        if (resLength >= 1) {
            qfFormula = results[0].AsBoolExpr();
        }
        for (int i = 1; i < resLength; i++) {
            qfFormula = ctx.mkOr(qfFormula, results[i].AsBoolExpr());
        }
        results = null;
        g = null;
        return (BoolExpr) qfFormula.simplify();
    }

    public BoolExpr elimITE(BoolExpr be, Context ctx) {
        Tactic elimIte = ctx.mkTactic("elim-term-ite");
        Goal g = ctx.mkGoal(false, false, false);
        g.add(be);
        BoolExpr iteFreeFormula = ctx.mkFalse();
        Goal[] results = elimIte.apply(g).getSubgoals();
        for (Goal res : results) {
            iteFreeFormula = ctx.mkOr(iteFreeFormula, res.AsBoolExpr());
        }
//        return (BoolExpr) iteFreeFormula.simplify();
        return iteFreeFormula;

    }

    //makes a clone of a solver s
    public Solver getSolverClone(Solver s, Context ctx) {
        Solver newSolver = ctx.mkSolver();
        BoolExpr[] beList = s.getAssertions();
        for (int i = 0; i < beList.length; i++) {
            newSolver.add(beList[i]);
        }
        return newSolver;
    }

    //copy assertions from s to t and returns t
    public Solver copySolverFromTo(Solver s, Solver t, Context ctx) {
        BoolExpr[] beList = s.getAssertions();
        for (int i = 0; i < beList.length; i++) {
            t.add(beList[i]);
        }
        return t;
    }

    public BoolExpr computeInterpolant(BoolExpr a, BoolExpr b, InterpolationContext ictx) {
        Params params = ictx.mkParams();
        BoolExpr ia = ictx.MkInterpolant(a); //creating interpolation point
        BoolExpr pat = ictx.mkAnd(ia, b);
        ComputeInterpolantResult cir = ictx.ComputeInterpolant(pat, params);
        if (cir.interp == null) {
            System.out.println("there is no interpolant, maybe the constraints are satisfiable");
            return null;
        }
        if (cir.interp.length == 0) {
            System.out.println("no interpolant derived");
            return null;
        }
        return cir.interp[0]; //we are interested in a single interpolant
    }

    public static void main(String[] args) {
        String fileName = "test.smt2";

        Z3Interface z3 = new Z3Interface();
        InterpolationContext ctx = z3.getInerpolationContext();
        long beginT = System.currentTimeMillis();
        BoolExpr be = z3.readSMTLIB2File(fileName, ctx);
        Expr[] formulaAandFormulaB = z3.getFormulasAandB(be);
        BoolExpr formulaA = (BoolExpr) formulaAandFormulaB[0];
        //formulaA = z3.preProcessQFBVFormulas(ctx, formulaA);
        BoolExpr formulaB = (BoolExpr) formulaAandFormulaB[1];
        //formulaB = z3.preProcessQFBVFormulas(ctx, formulaB);
        //System.out.println("formulaA "+formulaA);
        //System.out.println("formulaB "+formulaB);
        long endT = System.currentTimeMillis();
         System.out.println("bv interpolant: "+ z3.computeInterpolant(formulaA, formulaB, ctx));
        System.out.println("time= " + (endT - beginT) + " ms.");
        //System.out.println("qe " + qfF);
    }

}
