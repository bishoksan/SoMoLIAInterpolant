/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import gurobi.GRB;
import gurobi.GRB.StringAttr;
import gurobi.GRBConstr;
import gurobi.GRBEnv;
import gurobi.GRBException;
import gurobi.GRBLinExpr;
import gurobi.GRBModel;
import java.util.ArrayList;
import java.util.logging.Level;
import java.util.logging.Logger;

/**
 *
 * @author kafle
 */
public class GurobiInterface {

    public GRBEnv createGRBEnv() {
        GRBEnv env = null;
        try {
            env = new GRBEnv();
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return env;

    }

    public GRBModel getGRBModel(GRBEnv env) {
        GRBModel model = null;
        try {
            model = new GRBModel(env);
            //control the output flag
            model.getEnv().set(GRB.IntParam.OutputFlag, 0); //disable 0 /enable 1 screen printing
//            //seting parameter to the model, the following 5 were set
//            model.getEnv().set(GRB.DoubleParam.IntFeasTol, 1e-9);//https://www.gurobi.com/documentation/6.5/refman/intfeastol.html#parameter:IntFeasTol
//            model.getEnv().set(GRB.DoubleParam.FeasibilityTol, 1e-9);
            model.getEnv().set(GRB.IntParam.NumericFocus, 3); //https://www.gurobi.com/documentation/6.5/refman/numericfocus.html
//            model.getEnv().set(GRB.IntParam.MIPFocus, 1);//http://www.gurobi.com/documentation/6.0/refman/mipfocus.html#parameter:MIPFocus
//            model.getEnv().set(GRB.IntParam.Presolve, 1); //http://www.gurobi.com/documentation/6.5/refman/presolve.html

            //grbModel.getEnv().set(GRB.DoubleParam.OptimalityTol, 1e-9);
            //model.getEnv().set(GRB.IntParam.LazyConstraints, 1);
            //grbModel.getEnv().set(GRB.IntParam.SubMIPNodes, Integer.MAX_VALUE); //https://www.gurobi.com/documentation/6.5/refman/submipnodes.html#parameter:SubMIPNodes
            //model.getEnv().set(GRB.DoubleParam.Heuristics, 1);
            //grbModel.getEnv().set(GRB.IntParam.Presolve, 2);
            //grbModel.getEnv().set(GRB.IntParam.Aggregate,0);
            //model.getEnv().set(GRB.DoubleParam.MarkowitzTol, 0.999);
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return model;
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

    /**
     * Reset the model to an unsolved state, discarding any previously computed
     * solution information.
     */
    public GRBModel resetModel(GRBModel model) {
        try {
            model.reset();
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return model;
    }

    public GRBLinExpr createGRBLinExpr() {
        return new GRBLinExpr();
    }

    public GRBModel GRBSetMaximize(GRBLinExpr expr, GRBModel model) {
        try {
            model.setObjective(expr, GRB.MAXIMIZE);

        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        } catch (Exception e) {
            e.printStackTrace();
        }
        return model;
    }

    public double getOptValue(GRBModel model) {
        Double obj = null;
        try {
            obj = model.get(GRB.DoubleAttr.ObjVal);

        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return obj;
    }

    public GRBModel GRBSetMinimize(GRBLinExpr expr, GRBModel model) {
        try {
            model.setObjective(expr, GRB.MINIMIZE);

        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return model;
    }

    public static String exprString(GRBLinExpr expr) {
        String acc = "";
        int exprSize = expr.size();
        try {
            for (int i = 0; i < exprSize; i++) {
                long coeff = (long) expr.getCoeff(i);
                if (coeff != 1) {
                    acc = acc + coeff + " * " + expr.getVar(i).get(StringAttr.VarName) + " + ";
                } else {
                    acc = acc + expr.getVar(i).get(StringAttr.VarName) + " + ";
                }
            }
            long constant = (long) expr.getConstant();
            if (constant == 0) {
                acc = acc.trim();
                if (acc.isEmpty()) {
                    acc = "0";
                } else {
                    int k = acc.lastIndexOf("+");
                    if (k != -1) {
                        acc = acc.substring(0, k);
                    }
                }
            } else {
                acc += constant;
            }
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return acc;
    }

    public static String constrString(GRBLinExpr expr1, String op, GRBLinExpr expr2) {
        String acc = "";
        acc = exprString(expr1) + " " + op + " " + exprString(expr2);
        return acc;
    }

    public static long getRHSConstraint(String constraintName, GRBModel model) {
        long l = 0;
        try {
            GRBConstr c = model.getConstrByName(constraintName);
            l = (long) c.get(GRB.DoubleAttr.RHS);
            //System.out.println("the rhs of "+constraintName + " is "+l);
        } catch (GRBException ex) {
            Logger.getLogger(GurobiInterface.class.getName()).log(Level.SEVERE, null, ex);
        }
        return l;
    }

    public static String getConstraintIneqSign(GRBConstr c) {
        try {
            char a = c.get(GRB.CharAttr.Sense);
            return String.valueOf(a);
        } catch (GRBException ex) {
        }
        return null;
    }

    public int optimize(GRBModel model) {
        int status = 15; //none of the predefined status https://www.gurobi.com/documentation/6.5/refman/optimization_status_codes.html 
        try {
            model.optimize();
            status = model.get(GRB.IntAttr.Status);

        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return status;
    }

    public String[] getUnsatCore(GRBModel model) {
        //System.out.println("constraint size " + model.getConstrs().length);
        ArrayList<String> unsatCore = new ArrayList<>();
        try {
            model.computeIIS();
            //model.write("model.ilp");
            for (GRBConstr c : model.getConstrs()) {
                if (c.get(GRB.IntAttr.IISConstr) > 0) {
                    unsatCore.add(c.get(StringAttr.ConstrName));
                }
            }
        } catch (GRBException ex) {
            System.out.println("Error code: " + ex.getErrorCode() + ". "
                    + ex.getMessage());
        }
        return unsatCore.toArray(new String[unsatCore.size()]);
    }

    public void removeConstraint(GRBModel m, String constraintName) {
        try {
            GRBConstr c = m.getConstrByName(constraintName);
            if (c != null) {
                m.remove(c);
//                System.out.println("=====removed constraints===== "+constraintName);
            }
        } catch (GRBException e) {
            e.printStackTrace();

        }
    }

    public void removeConstraint(GRBModel m, GRBConstr c) {
        try {
            m.remove(c);
        } catch (GRBException e) {
            e.printStackTrace();

        }

    }

    public static GRBConstr getGrbConstraintByName(GRBModel m, String name) {
        try {
            return m.getConstrByName(name);
        } catch (GRBException e) {
            e.printStackTrace();

        }
        return null;
    }

    public void grbWrite(GRBModel grbModel, String fileName) {
        try {
            grbModel.write(fileName);
        } catch (GRBException e) {
            e.printStackTrace();
        }
    }

    public boolean evalConstraintInModel(GRBLinExpr e1, String operator, GRBLinExpr e2) {
        try {
//            System.out.println("operator "+operator);
//            System.out.println(" e1 "+e1.getValue());
            long d1 = (long) e1.getValue(); //returns a value of the expr from the model
            if (e1.getValue() % 1 != 0) { //ensuring integer value
                return false;
            }
//            System.out.println("d1 "+d1);
//            System.out.println(" e2 "+e2.getValue());
            long d2 = (long) e2.getValue();
            if (e2.getValue() % 1 != 0) {
                return false;
            }
//            System.out.println("d2 "+d2);
            //take modulo of both
            d1 %= Util.modulo_m();
            d2 %= Util.modulo_m();
//            System.out.println(" d1 d2 " + d1 + " " + d2);
            if (d1 < Util.min_neg()) {
                d1 = Util.modulo_m() + d1;
            }
            if (d2 < Util.min_neg()) {
                d1 = Util.modulo_m() + d2;
            }
            if (operator.equals("=")) {
                return d1 == d2;
            } else if (operator.equals(">=")) {
                return d1 >= d2;
            }
            if (operator.equals("<=")) {
                return d1 <= d2;
            }
        } catch (GRBException ex) {
        }
        return false;
    }

    public void disposeEnv(GRBEnv env) throws GRBException {
        env.dispose();
    }

    public void disposeModel(GRBModel model) throws GRBException {
        model.dispose();
    }

}
