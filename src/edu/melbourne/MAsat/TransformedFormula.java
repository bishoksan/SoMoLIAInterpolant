/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.BoolExpr;
import com.microsoft.z3.IntExpr;
import java.util.ArrayList;
import java.util.HashSet;

/**
 *
 * @author kafle
 */
public class TransformedFormula {

    BoolExpr originalFormula; //bit-vector formula
    BoolExpr formulaWModulo; //needed for checking sat in a model, lia form of the original, if the original formula is in bv form we do not need this
    int status; //0 =not trasformed, 1=transformed
    ArrayList<ArithFormula> formula;
    int formulaSize; //size of formula in LIA 
    HashSet<IntExpr> vars;
    HashSet<BvVariable> bvVars;
    boolean alreadyInTransformedFormInThesolver; //is already in a transformed form in the solver
    BoolExpr arithExprWQuantDeltas; //Full LIA expr. quantified with deltas
    BoolExpr arithFormulaWoDeltas; // delta free arithmetic formula
    boolean precise; //if the formula is in precise form in the solver
    boolean deltaIntroduced; //indicates whether deltas were introduced for this constraint

    public TransformedFormula() {
    }

    public TransformedFormula(ArrayList<ArithFormula> formula, int formulaSize) {
        this.formula = formula;
        this.formulaSize = formulaSize;
    }

    public int getFormulaSize() {
        return formulaSize;
    }

    public void setFormulaSize(int formulaSize) {
        this.formulaSize = formulaSize;
    }

    public ArrayList<ArithFormula> getFormula() {
        return formula;
    }

    public void setFormula(ArrayList<ArithFormula> formula) {
        this.formula = formula;
    }

    public TransformedFormula(BoolExpr originalFormula, int status, ArrayList<ArithFormula> formula, int formulaSize) {
        this.originalFormula = originalFormula;
        this.status = status;
        this.formula = formula;
        this.formulaSize = formulaSize;
    }

    public BoolExpr getOriginalFormula() {
        return originalFormula;
    }

    public void setOriginalFormula(BoolExpr originalFormula) {
        this.originalFormula = originalFormula;
    }

    public int getStatus() {
        return status;
    }

    public void setStatus(int status) {
        this.status = status;
    }

    public BoolExpr getFormulaWModulo() {
        return formulaWModulo;
    }

    public void setFormulaWModulo(BoolExpr formulaWModulo) {
        this.formulaWModulo = formulaWModulo;
    }

    public TransformedFormula(BoolExpr originalFormula) {
        this.originalFormula = originalFormula;
    }

    public TransformedFormula(BoolExpr originalFormula, int status) {
        this.originalFormula = originalFormula;
        this.status = status;
    }

    public TransformedFormula(BoolExpr originalFormula, BoolExpr formulaWModulo, int status) {
        this.originalFormula = originalFormula;
        this.formulaWModulo = formulaWModulo;
        this.status = status;
    }

    public HashSet<IntExpr> getVars() {
        return vars;
    }

    public void setVars(HashSet<IntExpr> vars) {
        this.vars = vars;
    }

//    public TransformedFormula(BoolExpr originalFormula, int status, HashSet<IntExpr> vars) {
//        this.originalFormula = originalFormula;
//        this.status = status;
//        this.vars = vars;
//    }
      public TransformedFormula(BoolExpr originalFormula, int status, HashSet<BvVariable> vars) {
        this.originalFormula = originalFormula;
        this.status = status;
        this.bvVars = vars;
    }

    public boolean isAlreadyInTransformedFormInThesolver() {
        return alreadyInTransformedFormInThesolver;
    }

    public void setAlreadyInTransformedFormInThesolver(boolean alreadyInTransformedFormInThesolver) {
        this.alreadyInTransformedFormInThesolver = alreadyInTransformedFormInThesolver;
    }

    public BoolExpr getArithFormulaWoDeltas() {
        return arithFormulaWoDeltas;
    }

    public void setArithFormulaWoDeltas(BoolExpr arithFormulaWoDeltas) {
        this.arithFormulaWoDeltas = arithFormulaWoDeltas;
    }

    public boolean isPrecise() {
        return precise;
    }

    public void setPrecise(boolean precise) {
        this.precise = precise;
    }

    public boolean isDeltaIntroduced() {
        return deltaIntroduced;
    }

    public void setDeltaIntroduced(boolean deltaIntroduced) {
        this.deltaIntroduced = deltaIntroduced;
    }

    public BoolExpr getArithExprWQuantDeltas() {
        return arithExprWQuantDeltas;
    }

    public void setArithExprWQuantDeltas(BoolExpr arithExprWQuantDeltas) {
        this.arithExprWQuantDeltas = arithExprWQuantDeltas;
    }
    
    
}
