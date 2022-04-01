/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.IntExpr;

/**
 *
 * @author bishoksank
 */
public class OptDeltaValues {

    IntExpr delta;
    IntExpr min;
    IntExpr max;

    public OptDeltaValues(IntExpr delta, IntExpr min, IntExpr max) {
        this.delta = delta;
        this.min = min;
        this.max = max;
    }

    public OptDeltaValues() {
    }

    public OptDeltaValues(IntExpr delta) {
        this.delta = delta;
    }

    public IntExpr getDelta() {
        return delta;
    }

    public void setDelta(IntExpr delta) {
        this.delta = delta;
    }

    public IntExpr getMin() {
        return min;
    }

    public void setMin(IntExpr min) {
        this.min = min;
    }

    public IntExpr getMax() {
        return max;
    }

    public void setMax(IntExpr max) {
        this.max = max;
    }

}
