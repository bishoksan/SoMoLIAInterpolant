/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package edu.melbourne.MAsat;

import com.microsoft.z3.Symbol;

/**
 *
 * @author bishoksank
 */
public class BvVariable {
    Symbol name;
    int sortSize;

    public BvVariable(Symbol name, int sortSize) {
        this.name = name;
        this.sortSize = sortSize;
    }

    public Symbol getName() {
        return name;
    }

    public void setName(Symbol name) {
        this.name = name;
    }

    public int getSortSize() {
        return sortSize;
    }

    public void setSortSize(int sortSize) {
        this.sortSize = sortSize;
    }
    
    
}
