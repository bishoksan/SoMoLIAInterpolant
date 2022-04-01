/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import gurobi.GRBLinExpr;

/**
 *
 * @author kafle
 */
public class ConstraintGRB {
    
    GRBLinExpr lhs; 
    GRBLinExpr rhs; 
    char operator;

    public ConstraintGRB(GRBLinExpr lhs, GRBLinExpr rhs, char operator) {
        this.lhs = lhs;
        this.rhs = rhs;
        this.operator = operator;
    }

    public GRBLinExpr getLhs() {
        return lhs;
    }

    public void setLhs(GRBLinExpr lhs) {
        this.lhs = lhs;
    }

    public GRBLinExpr getRhs() {
        return rhs;
    }

    public void setRhs(GRBLinExpr rhs) {
        this.rhs = rhs;
    }

    public char getOperator() {
        return operator;
    }

    public void setOperator(char operator) {
        this.operator = operator;
    }
    
    
    
}
