/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.BoolExpr;
import org.apache.log4j.PropertyConfigurator;

/**
 *
 * @author kafle
 */
public class Message {

    Witness w;
    long time;

    public static String showStatistics(String file, Witness w, long time, int nrConstraints, int refinementCount, int nrConstraintRelaxed, boolean genWitness) {
        String output;
        if (w.isSatisfiable()) {
            if (genWitness) {
                output = "\n{File=" + file + ",  Result=SAT, #constrs=" + nrConstraints + ", #refinements=" + refinementCount + ", #constrRelaxed=" + nrConstraintRelaxed + ", Time=" + time + " ms, Model= \n" + w.getModel() + "}";
                //Z3Interface.logger.debug(output);
            } else {
                output = "\n{File=" + file + ",  Result=SAT, #constrs=" + nrConstraints + ", #refinements=" + refinementCount + ", #constrRelaxed=" + nrConstraintRelaxed + ", Time=" + time + " ms}\n";
                //Z3Interface.logger.info(output);
            }
        } else {
            if (genWitness) {
                output = "\n{File=" + file + ",  Result=UNSAT, #constrs=" + nrConstraints + ", #refinements=" + refinementCount + ", #constrRelaxed=" + nrConstraintRelaxed + ", Time=" + time + " ms, UnsatCore="
                        + printUnsatCore(w.getUnsatCore()) + "}";
                //Z3Interface.logger.debug(output);
            } else {
                output = "\n{File=" + file + ",  Result=UNSAT, #constrs=" + nrConstraints + ", #refinements=" + refinementCount + ", #constrRelaxed=" + nrConstraintRelaxed + ", Time=" + time + " ms}\n";
                //Z3Interface.logger.info(output);
            }
        }
//        if (w.isSatisfiable()) {
//            output = "sat";
//        } else {
//            output = "unsat";
//        }
        return output;
    }

    public static String showQEStatistics(String file, long time, int nrConstraints, int refinementCount, int nrConstraintRelaxed) {
        String output;
        output = "\n{File=" + file + ",  #constrs=" + nrConstraints + ", #refinements=" + refinementCount + ", #constrRelaxed=" + nrConstraintRelaxed + ", Time=" + time + " ms}";
                //Z3Interface.logger.debug(output);

        return output;
    }

    public static String printUnsatCore(String[] exprs) {
        String output;
        output = "[";
        for (int i = 0; i < exprs.length; i++) {
            if (i != exprs.length - 1) {
                output = output + exprs[i] + ", ";
            } else {
                output += exprs[i];
            }
        }
        output += "]";
        return output;
    }

    public static void printAssertions(BoolExpr[] be) {
        for (int i = 0; i < be.length; i++) {
            System.out.println("ass  " + i + " " + be[i]);
        }
    }

    public static void configureLogger() {
        PropertyConfigurator.configure("log4j.properties");
    }

}
