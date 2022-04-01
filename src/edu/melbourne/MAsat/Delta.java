/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.IntExpr;

/**
 *
 * @author kafle
 */
public class Delta {
    IntExpr var;
    IntExpr value;

    public Delta(IntExpr var, IntExpr value) {
        this.var = var;
        this.value = value;
    }

    public Delta(IntExpr var) {
        this.var = var;
    }
    

    public IntExpr getVar() {
        return var;
    }

    public void setVar(IntExpr var) {
        this.var = var;
    }

    public IntExpr getValue() {
        return value;
    }

    public void setValue(IntExpr value) {
        this.value = value;
    }

     
}
