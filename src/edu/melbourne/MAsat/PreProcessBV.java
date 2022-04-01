/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.*;
import java.io.FileWriter;
import java.io.IOException;
import java.util.HashSet;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author bishoksank
 */
public class PreProcessBV {

    boolean findBVSize = true;

    HashSet<String> variables = new HashSet<>();
    int extractVarCount = 0;

    public BoolExpr translateToLIA(Context ctx, BoolExpr bExpr) {
        BoolExpr[] liaFormulas = null;
        BoolExpr formulas;
        Sort[] intVarSorts = null;
        Symbol[] varNames = null;
        try {
            if (bExpr.isQuantifier()) {
                Quantifier q = (Quantifier) bExpr;
                varNames = q.getBoundVariableNames(); //bound variable are ordered top-down
                intVarSorts=q.getBoundVariableSorts();
                int nrBoundVars = varNames.length;
                Expr[] bvVarExpr = new Expr[nrBoundVars];
                Expr[] intVarExpr = new Expr[nrBoundVars];
                for (int i = 0; i < varNames.length; i++) {
                    intVarExpr[nrBoundVars - 1 - i] = ctx.mkIntConst(varNames[i]); //reversing the list
                    bvVarExpr[nrBoundVars - 1 - i] = ctx.mkBVConst(varNames[i], ((BitVecSort) intVarSorts[i]).getSize()); //change it with appropriate bit
                }
                //create integers sort
                intVarSorts = new Sort[nrBoundVars];
                Sort intSort = ctx.mkIntSort();
                for (int i = 0; i < varNames.length; i++) {
                    intVarSorts[i] = intSort; //reversing the list
                }
                BoolExpr qBody = q.getBody();
                qBody = (BoolExpr) qBody.substituteVars(bvVarExpr);
                formulas = qBody;
            } else {
                formulas = bExpr;
            }

            Expr[] exprs;
            if (formulas.isAnd()) {
                exprs = formulas.getArgs();
            } else {
                //System.out.println("is not a conjunctions ========= !");
                exprs = new Expr[1];
                exprs[0] = formulas;
            }
            int formulaCount = exprs.length;
            liaFormulas = new BoolExpr[formulaCount];
            for (int i = 0; i < formulaCount; i++) {
                BoolExpr beLIA = (BoolExpr) exprs[i];
                // System.out.println("bv formula  " + beLIA);
                BoolExpr beBV = translateTerm(beLIA, ctx);
                liaFormulas[i] = beBV;
            }

        } catch (Exception e) {
            e.printStackTrace();
        }
        BoolExpr liaForm = Util.listToBF(ctx, liaFormulas);
        if (bExpr.isQuantifier()) {
            liaForm = getFormulaWBoundVars(ctx, liaForm, varNames);
            liaForm = ctx.mkExists(intVarSorts, varNames, liaForm, 0, null, null, null, null);
        }
        return liaForm;
    }

    public BoolExpr translateTerm(BoolExpr be, Context ctx) {
        IntExpr zero = ctx.mkInt(0);
        IntExpr one = ctx.mkInt(1);
        Expr var;
        if (be.isFalse() || be.isTrue()) {
            return be;
        }
        //at the moment limit it to bit vectors
        if (be.isDistinct()) {//Indicates whether the term is an n-ary distinct predicate (every argument is mutually distinct).
            return convertBVFToLIAF(be, ctx);
        }
        if (isBVOperation(be)) {
            return convertBVFToLIAF(be, ctx);
        }
        if (be.isOr()) {
            return translateOr(be, ctx);
        }
        if (be.isAnd()) {
            return translateAnd(be, ctx);
        }
        //System.out.println("be is "+be);
        if (be.isNot()) {
            //System.out.println("to neg expr "+be);
            BoolExpr negExpr = translateNot(be, ctx);
            //System.out.println("negated expr "+negExpr);
            return negExpr;
        }
        //is a variable
        if (be.isConst()) { //is a boolean variable
            IntExpr ie = ctx.mkIntConst(be.toString());
            variables.add(be.toString());
            return ctx.mkAnd(ctx.mkLe(zero, ie), ctx.mkLe(ie, one));
        }
        System.out.println("unrecognized formula " + be);
        return null;
    }

    public BoolExpr translateNot(BoolExpr be, Context ctx) { //assumming nnf
        IntExpr zero = ctx.mkInt(0);
        IntExpr one = ctx.mkInt(1);
        BoolExpr notTrue = ctx.mkNot(ctx.mkTrue());
        Expr var;
        var = be.getArgs()[0];
        if (((BoolExpr) var).isTrue()) {
            return ctx.mkFalse();
        }
        if (((BoolExpr) var).isFalse()) {
            return ctx.mkTrue();
        }
        if (var.isConst()) {
            //this is a variable
            //System.out.println("be is "+var);
            String notVar = var.toString() + "_not";
            variables.add(notVar);
            IntExpr ieNot = ctx.mkIntConst(notVar);
            IntExpr ie = ctx.mkIntConst(var.toString());
            if (variables.contains(var.toString())) { //this exprs already contains the non-negated var
                //create new var y and write y=1-x
                return ctx.mkEq(ieNot, ctx.mkSub(one, ie));
            } else {
                //add that variable
                variables.add(var.toString());
                return ctx.mkAnd(ctx.mkLe(zero, ie), ctx.mkLe(ie, one), ctx.mkEq(ieNot, ctx.mkSub(one, ie)));
            }
        } else {
            //is not a boolean variable
            // System.out.println("var expr ========"+var);
            BoolExpr arithIneq = translateTerm((BoolExpr) var, ctx);
            // System.out.println("arith expr ======"+arithIneq);
            Expr[] exprs = arithIneq.getArgs();
            //System.out.println("expr 0 "+exprs[0]);
            ArithExpr a0 = (ArithExpr) exprs[0];
            ArithExpr a1 = (ArithExpr) exprs[1];
            BoolExpr retExpr = null;
            if (arithIneq.isLT()) {
                retExpr = ctx.mkGe(a0, a1);
            } else if (arithIneq.isLE()) {
                retExpr = ctx.mkGt(a0, a1);
            } else if (arithIneq.isGT()) {
                retExpr = ctx.mkLe(a0, a1);
            } else if (arithIneq.isGE()) {
                retExpr = ctx.mkLt(a0, a1);
            } else if (arithIneq.isEq()) {
                retExpr = ctx.mkNot(arithIneq);
            }
            //System.out.println("coming here ======"+retExpr);
            return retExpr;
        }
    }

    public BoolExpr translateAnd(BoolExpr be, Context ctx) {
        BoolExpr beAnd = ctx.mkTrue();
        Expr[] andExprs;
        //System.out.println("and expr ====== "+be);
        andExprs = be.getArgs();
        if (andExprs.length > 0) {
            beAnd = translateTerm((BoolExpr) andExprs[0], ctx);
        }
        for (int i = 1; i < andExprs.length; i++) {
            beAnd = ctx.mkAnd(beAnd, translateTerm((BoolExpr) andExprs[i], ctx));
        }
        return beAnd;
    }

    public BoolExpr translateOr(BoolExpr be, Context ctx) {
        BoolExpr beOr = ctx.mkFalse();
        Expr[] orExprs;
        orExprs = be.getArgs();
        if (orExprs.length > 0) {
            beOr = translateTerm((BoolExpr) orExprs[0], ctx);
        }
        for (int i = 1; i < orExprs.length; i++) {
            beOr = ctx.mkOr(beOr, translateTerm((BoolExpr) orExprs[i], ctx));
        }
        return beOr;
    }

    public void writeLIAHeader(FileWriter fw) {
        try {
            fw.write("(set-logic QF_LIA) \n \n");
            for (String ie : variables) {
                fw.write("(declare-fun " + ie + " () Int) \n");
            }
            fw.write(" \n");
        } catch (IOException ex) {
            Logger.getLogger(PreProcessBV.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    public void writeLIAAssertions(FileWriter fw, BoolExpr[] bvFormulas) {
        try {
            for (int i = 0; i < bvFormulas.length; i++) {
                BoolExpr beLIA = bvFormulas[i];
                fw.write("(assert " + beLIA.toString() + ")\n");
            }
            fw.write("\n");
        } catch (IOException ex) {
            Logger.getLogger(PreProcessBV.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    public void writeLIATail(FileWriter fw) {
        try {
            fw.write("(check-sat)");
        } catch (IOException ex) {
            Logger.getLogger(PreProcessBV.class.getName()).log(Level.SEVERE, null, ex);
        }
    }

    public boolean isBVOperation(BoolExpr beBV) {
        return (beBV.isEq() || beBV.isBVULE() || beBV.isBVULT() || beBV.isBVUGT() || beBV.isBVUGE());
    }

    public BoolExpr convertBVFToLIAF(BoolExpr beBV, Context ctx) {
        IntExpr zero = ctx.mkInt(0);
        IntExpr one = ctx.mkInt(1);
        IntExpr ie1, ie2;
        BoolExpr be1, be2, be;
        Expr[] bvExprs = beBV.getArgs();
        //if operands are boolean vars
        if (bvExprs[0].isBool() && bvExprs[1].isBool()) { //this case can only be equality
            ie1 = ctx.mkIntConst(bvExprs[0].toString());
            be1 = ctx.mkAnd(ctx.mkLe(zero, ie1), ctx.mkLe(ie1, one));
            ie2 = ctx.mkIntConst(bvExprs[0].toString());
            be2 = ctx.mkAnd(ctx.mkLe(zero, ie1), ctx.mkLe(ie1, one));
            return ctx.mkEq(be1, be2);
        }
        BitVecExpr ae0 = (BitVecExpr) bvExprs[0];
//        if (findBVSize) {//discovering bv size
//            //System.out.println("sort size " + ae0.getSortSize());
//            Main.setINT_WIDTH(ae0.getSortSize());
//            findBVSize = false;
//        }
        // System.out.println("left" + ae0);
        BitVecExpr ae1 = (BitVecExpr) bvExprs[1];
        //System.out.println("right " + ae1);
        ArithExpr left = (ArithExpr) convertToLIAExpr(ae0, ctx).simplify();
        ArithExpr right = (ArithExpr) convertToLIAExpr(ae1, ctx).simplify();
        //System.out.println("right " + ae1);
        if (beBV.isEq()) {
            return ctx.mkEq(left, right);
        }
        if (beBV.isBVULE()) {
            return ctx.mkLe(left, right);
        }
        if (beBV.isBVULT()) {
            return ctx.mkLt(left, right);
        }
        if (beBV.isBVUGT()) {
            return ctx.mkGt(left, right);
        }
        if (beBV.isBVUGE()) {
            return ctx.mkGe(left, right);
        }
        //only consider binary distinct
        if (beBV.isDistinct()) {
            return ctx.mkOr(ctx.mkGt(left, right), ctx.mkLt(left, right));
        }

        //at times as a result of Z3-preprocessing some boolean vars are created, translateToLIA them as 0<=var<=1
        BoolExpr ie = ctx.mkBoolConst(beBV.toString());
        return ie;
    }

    public boolean isUnaryMinus(ArithExpr linExpr) {
        boolean isUnaryMinus = linExpr.isApp() && linExpr.getNumArgs() == 1 && ((ArithExpr) linExpr.getArgs()[0]).isIntNum();
        return isUnaryMinus;
    }

//     public int intExprtoInt(ArithExpr ae){
//        
//    }
    //arithmetic bit vector operations
    public ArithExpr convertToLIAExpr(BitVecExpr bvExpr, Context ctx) {
        //System.out.println("expression " + bvExpr);
        Expr[] exprs;
        try {

            if (bvExpr.isConst() && bvExpr.isBV()) //is bv variable
            {
                // System.out.println("is variable "+bvExpr);
                variables.add(bvExpr.getSExpr());
                return ctx.mkIntConst(bvExpr.toString());
            }
            if (bvExpr.isBVAdd()) {
                exprs = bvExpr.getArgs();
                ArithExpr arithAcc = ctx.mkInt(0);
                for (Expr e : exprs) {
                    arithAcc = ctx.mkAdd(arithAcc, convertToLIAExpr((BitVecExpr) e, ctx));
                }
                return arithAcc;
            }
            if (bvExpr.isBVSub()) {
                exprs = bvExpr.getArgs();
                ArithExpr arithAcc = ctx.mkInt(0);
                for (int i = 0; i < exprs.length; i++) {
                    if (i == 0) {
                        // System.out.println("expr 0 " + exprs[i]);
                        arithAcc = ctx.mkAdd(arithAcc, convertToLIAExpr((BitVecExpr) exprs[i], ctx));
                    } else {
                        // System.out.println("expr 1 " + exprs[i]);
                        arithAcc = ctx.mkSub(arithAcc, convertToLIAExpr((BitVecExpr) exprs[i], ctx));
                    }
                }
                return arithAcc;
            }

            if (bvExpr.isBVMul()) {
                exprs = bvExpr.getArgs();
                ArithExpr arithAcc = ctx.mkInt(1);
                int length=exprs.length;
                if(length>0){
                    arithAcc= convertToLIAExpr((BitVecExpr) exprs[0], ctx);
                }
                for (int i=1; i<length; i++) {
                    arithAcc = ctx.mkMul(arithAcc, convertToLIAExpr((BitVecExpr) exprs[i], ctx));
                }
                return arithAcc;
            }
            if (bvExpr.isBVExtract()) {
                //System.out.println("bvExpr "+bvExpr);
                //int low = ((BitVecExpr) bvExpr).getSortSize();
                //System.out.println(" extract "+bvExpr.getArgs()[0]);
                return convertToLIAExpr((BitVecExpr) bvExpr.getArgs()[0], ctx);
            }
            if (bvExpr.isBVUMinus()) {
                IntExpr modulo = ctx.mkInt(Util.modulo_m());
                return ctx.mkSub(modulo, convertToLIAExpr((BitVecExpr) bvExpr.getArgs()[0], ctx));
            }

            if (bvExpr.isBVShiftLeft()) {
                exprs = bvExpr.getArgs(); //assume that exprs[0] is a variable and exprs[1] is a constant
                long bit = 0;
                try {
                    bit = Long.parseLong(exprs[1].toString());
                } catch (NumberFormatException e) {
                    System.out.println("left shift by a variable not possible");
                }
                IntNum power = ctx.mkInt((long) Math.pow(2, bit));
                return ctx.mkMul(convertToLIAExpr((BitVecExpr) exprs[0], ctx), power);
            }
            if (bvExpr.isBVConcat()) {// t=t1::t2 => x_t=2^m* x_t1 + x_t2
                //asumme concatenation of just 2 bit vector exprs
                exprs = bvExpr.getArgs();
                ArithExpr first = convertToLIAExpr((BitVecExpr) exprs[0], ctx);
                IntNum multiplier = ctx.mkInt(Util.modulo_m());
                first = ctx.mkMul(first, multiplier);
                ArithExpr second = convertToLIAExpr((BitVecExpr) exprs[1], ctx);
                return ctx.mkAdd(first, second);
            }
            if(bvExpr.isBVToInt()){
               
                 return ctx.mkBV2Int(bvExpr, false); //true indicates signed
            }
            //is  a constant number
            return ctx.mkInt(bvExpr.toString());
        } catch (Exception e) {
            e.printStackTrace();

        }
        return null;
    }
    /*
     bvTerm_[n][hi:lo]=newBVTerm_[hi-lo+1] equals the following LIA
     bvTerm=2^{hi+1}h + 2^lo*newBVTerm+l where h=[0, 2^{n-hi-1}-1], newBVTerm=[0, 2^{hi-lo+1}-1],l=[0, 2^hi -1]
     **/

    public ArithExpr bvExtractToInt(int originalBVSize, int hi, int lo, BitVecExpr bvExpr, Context ctx) {
        ArithExpr ae = ctx.mkInt(0);
        //checking if the top bit is equal to the bitsize, note that bit count starts from 0
        if (originalBVSize != hi + 1) {
            ArithExpr h = ctx.mkIntConst("h_" + extractVarCount);
            extractVarCount++;
            h = ctx.mkMul(ctx.mkInt((long) Math.pow(2, hi + 1)), h);
            ae = ctx.mkAdd(ae, h);
        }
        //checking if the lower bit is 0, assuming unsigned int
        if (lo != 0) {
            ArithExpr l = ctx.mkIntConst("l_" + extractVarCount);
            extractVarCount++;
            ae = ctx.mkAdd(ae, l);
        }
        //actual extraction part
        ArithExpr m = ctx.mkIntConst("m_" + extractVarCount);
        extractVarCount++;
        if (lo != 0) {
            m = ctx.mkMul(ctx.mkInt((long) Math.pow(2, lo)), m);
        }
        ae = ctx.mkAdd(ae, m);
        return ae;
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

}
