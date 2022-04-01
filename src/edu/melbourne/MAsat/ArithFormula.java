/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.ArithExpr;
import com.microsoft.z3.BoolExpr;
/**
 *
 * @author kafle
 */
public class ArithFormula {
    BoolExpr formula; //expression in Ax<=b form
    ArithExpr deltaExpr; //expression in delta (d2-d1 or some form)
    boolean equality; //indicates if formula is equality or not

    public ArithFormula(BoolExpr formula, ArithExpr deltaExpr, boolean equality) {
        this.formula = formula;
        this.deltaExpr = deltaExpr;
        this.equality = equality;
    }

    public boolean isEquality() {
        return equality;
    }

    public void setEquality(boolean equality) {
        this.equality = equality;
    }

    public BoolExpr getFormula() {
        return formula;
    }

    public void setFormula(BoolExpr formula) {
        this.formula = formula;
    }

    public ArithExpr getDeltaExpr() {
        return deltaExpr;
    }

    public void setDeltaExpr(ArithExpr deltaExpr) {
        this.deltaExpr = deltaExpr;
    }


    
}
