package edu.melbourne.MAsat;

import java.io.BufferedReader;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;

public class Main {

    public static int INT_WIDTH;
    public static String SMT_LOGIC = "QF_BV";
    public static final int DEFAULT_BIT = 32;
    public static final int THRESHOLD_BIT = 0; //If m>THRESHOLD_BIT then solve it using benders otherwise transform directly and solve

    public static void main(String[] args) throws IOException {
        if (args.length < 1) {
            System.err.println("Usage: progam <FileName> [<Int_width>]");
            System.exit(1);
        }
        String fileName = args[0].trim();
        SMT_LOGIC = getSMTLogic(fileName);
        if (fileName.endsWith(".smt")) { //is smtlib v1 file, 
            SMT_LOGIC = "BV";
            INT_WIDTH = 32;
        }
        if (SMT_LOGIC == null) {
            System.err.println("SMT-logic is not specified in the input file " + fileName + "");
            System.exit(2);
        }

        if (SMT_LOGIC.equals("QF_LIA") || SMT_LOGIC.equals("QF_IDL") || SMT_LOGIC.equals("LIA")) {
            if (args.length == 1) { //only file name is provided
                INT_WIDTH = DEFAULT_BIT; //32 bit is default
            } else if (args.length == 2) { //second argument is a bit-width/int-width
                INT_WIDTH = Integer.parseInt(args[1]);
            }
        }
        INT_WIDTH = 32; //remove this, need to deduce this from the BV constraints
        //does not use any pre-processing for BV theory
        new InterpolantBendersDecompWFixedSizeLazyWPPConj().computeMAInterpolant(fileName);
//         new QEBendersDecompWFixedSize().computeMAInterpolant(fileName);
    }

    public static String getSMTLogic(String inputFile) {
        BufferedReader fis = null;
        int begin, end;
        String command = "(set-logic";
        String line;
        try {
            fis = new BufferedReader(new FileReader(inputFile));
            while ((line = fis.readLine()) != null) {
                if (line.startsWith(command)) {
                    begin = command.length();
                    end = line.lastIndexOf(")");
                    return line.substring(begin, end).trim();
                }
            }

        } catch (FileNotFoundException ex) {
            ex.printStackTrace();
        } catch (IOException io) {
            io.printStackTrace();
        }
        try {
            fis.close();

        } catch (IOException ex) {
            ex.printStackTrace();
        }
        return null;
    }

    public static int getINT_WIDTH() {
        return INT_WIDTH;
    }

    public static void setINT_WIDTH(int INT_WIDTH) {
        Main.INT_WIDTH = INT_WIDTH;
    }

}
