/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import gurobi.GRBModel;

/**
 *
 * @author kafle
 */
public class Witness {
    
    boolean satisfiable; //satisfiable or not
    GRBModel model; //model is satisfiable
    String[] unsatCore; //in case of a conflicting constraint, unsat core contains a unique element

    public Witness(boolean satisfiable, GRBModel model, String[] unsatCore) {
        this.satisfiable = satisfiable;
        this.model = model;
        this.unsatCore = unsatCore;
    }

    public boolean isSatisfiable() {
        return satisfiable;
    }

    public void setSatisfiable(boolean satisfiable) {
        this.satisfiable = satisfiable;
    }

    public GRBModel getModel() {
        return model;
    }

    public void setModel(GRBModel model) {
        this.model = model;
    }

    public String[] getUnsatCore() {
        return unsatCore;
    }

    public void setUnsatCore(String[] unsatCore) {
        this.unsatCore = unsatCore;
    }

}