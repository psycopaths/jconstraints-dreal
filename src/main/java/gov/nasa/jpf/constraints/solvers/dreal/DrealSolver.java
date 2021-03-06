/*
 * Copyright (C) 2015, United States Government, as represented by the 
 * Administrator of the National Aeronautics and Space Administration.
 * All rights reserved.
 *
 * The PSYCO: A Predicate-based Symbolic Compositional Reasoning environment 
 * platform is licensed under the Apache License, Version 2.0 (the "License"); you 
 * may not use this file except in compliance with the License. You may obtain a 
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0. 
 *
 * Unless required by applicable law or agreed to in writing, software distributed 
 * under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR 
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the 
 * specific language governing permissions and limitations under the License.
 */
package gov.nasa.jpf.constraints.solvers.dreal;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.Scanner;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.SolverContext;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.solvers.dreal.DrealValuationResult.Interval;

public class DrealSolver extends ConstraintSolver {

  public static class DrealSolverBuilder {
    private String path;
    private IntervalSelectionMethod selectionMethod = IntervalSelectionMethod.RANDOM;
    private boolean useSeed = false;
    private int seed;
    
    public DrealSolverBuilder setDrealPath(String path) {
      this.path = path;
      return this;
    }
    
    public DrealSolverBuilder setSeed(int seed) {
      this.useSeed = true;
      this.seed = seed;
      return this;
    }
    
    public DrealSolverBuilder setIntervalSelectionMethod(IntervalSelectionMethod selectionMethod) {
      this.selectionMethod = selectionMethod;
      return this;
    }
    
    public DrealSolver build() {
      if(useSeed) {
        if(selectionMethod == IntervalSelectionMethod.RANDOM)
          return new DrealSolver(this.path, new RandomValueSelector(this.seed));
      }
      return new DrealSolver(this.path, this.selectionMethod);
    }
  }
  
  private String drealPath;
  private ValueSelector valSelector;
  
  
  private DrealSolver(String drealPath, ValueSelector valueSelector) {
    this.drealPath = drealPath;
    this.valSelector = valueSelector;
  }
  
  private DrealSolver(String drealPath, IntervalSelectionMethod selectionMethod) {
    this.drealPath = drealPath;
    switch(selectionMethod) {
    case NONE:
    case RANDOM:
    default:
    this.valSelector = new RandomValueSelector();
    }
  }
  
  @Override
  public SolverContext createContext() {
    return new DrealSolverContext(this);
  }
  
  public static Logger logger = Logger.getLogger("constraints");

  @Override
  public Result solve(Expression<Boolean> f, Valuation result) {
    DrealExpressionGenerator expGen = new DrealExpressionGenerator();
    String smtLibExp = expGen.generateAssertion(f);
    DrealResult res = this.solve(smtLibExp);
    Result r = res.getResult();
    if(r.equals(Result.SAT)) {
      Collection<Variable<?>> intv = expGen.getIntVars().values();
      setValuation(intv, res, result);
      
      Collection<Variable<?>> doublev = expGen.getDoubleVars().values();
      setValuation(doublev, res, result);
    }
    return r;
  }
  
  private void setValuation(Collection<Variable<?>> vars, DrealResult drealRes, Valuation res) {
    for(Variable<?> var : vars) {
      DrealValuationResult drealVal = drealRes.getValuation(var.getName());
      // drealVal can be null if the variable can be set to an arbitrary value
      // This is e.g. the case if for superfluous variable or in cases where a variable is x * 0
      //and does not appear anywhere else in the formula
      double concVal = 0.0;
      if(drealVal != null) { 
        Interval val = drealVal.getValuation();
        concVal = this.valSelector.getValue(val);
      }
      res.setParsedValue(var, ""+concVal);
    }
  }
 
  public DrealResult solve(String smtLibExp) {
    Process dreal = null;
    DrealResult drealRes = null;
    try {
      ProcessBuilder builder = new ProcessBuilder(drealPath,  "--model", "--in");
      builder.redirectErrorStream(true);
      dreal = builder.start();
      OutputStream out = dreal.getOutputStream();
      for(byte b : smtLibExp.getBytes())
        out.write(b);
      //out.write(smtLibExp.getBytes());
      out.close();
      DrealResultParser parser = new DrealResultParser(dreal.getInputStream());
      Thread t = new Thread(parser);
      t.start();
      dreal.waitFor();
      t.join();
      drealRes = parser.getResult();
    } catch (IOException e) {
      throw new DrealSolverException(e);
    } catch (InterruptedException e) {
      throw new DrealSolverException(e);
    }
    return drealRes;
  }
  
  /*
   * matches:
   *  x : [ ENTIRE ] = [ -INFTY ]
   *  y : [ ENTIRE ] = [-8.200000000000001, -8.199023437500001]
   */
  private static Pattern valuationPattern =  Pattern.compile("\\s*([a-zA-Z0-9]+)\\s*:\\s*\\[[a-zA-Z0-9\\s]*\\]\\s*=\\s*[\\[\\(]+([-0-9\\.e+-]+|\\s*-INFTY\\s*)\\s*,?\\s*([-0-9\\.e+-]+|\\s*-INFTY\\s)?\\s*[\\]\\)]+");
  
  private static class DrealResultParser implements Runnable {
    private InputStream in;
    private DrealResult result;
    public DrealResultParser(InputStream in) {
      this.in = in;
    }
    
    public DrealResult getResult() {
      return this.result;
    }
    
    @Override
    public void run() {
      BufferedReader rd = new BufferedReader(new InputStreamReader(in));
      List<DrealValuationResult> valuations = new LinkedList<>();
      Matcher matcher;
      String line = "", prevLine = "";
      try {
        while((line = rd.readLine()) != null) {
          matcher = valuationPattern.matcher(line);
          System.out.println(line);

          if(matcher.find()) {
            System.out.println("match " + matcher.group(0));
            System.out.println("val " + matcher.group(1));
            String varName = matcher.group(1);
            double vs = getDoubleFromStr(matcher.group(2).trim());
            double ve;
            if(Double.isInfinite(vs))
            	ve = vs;
            else
            	ve = getDoubleFromStr(matcher.group(3));
            valuations.add(new DrealValuationResult(varName, vs, ve));
          }
          prevLine = line;
        }
        Result jConstraintsResult = null;
        //TODO: Not the most robust way of parsing the result
        if(prevLine.startsWith("delta-sat")) {
          jConstraintsResult = Result.SAT;
          double delta = getDelta(prevLine);
          result = new DrealResult(jConstraintsResult, valuations, delta);
        } else {
          if(prevLine.equals("unsat"))
            jConstraintsResult = Result.UNSAT;
          else if(prevLine.equals("unknown"))
            jConstraintsResult = Result.DONT_KNOW;
          else 
            throw new DrealSolverException("Failed to parse dReal final result: " + prevLine);
          result = new DrealResult(jConstraintsResult);
        }
        in.close();
      } catch (IOException e) {
        throw new DrealSolverException(e);
      }
    }

    private double getDelta(String deltaSatResult) {
      Pattern p = Pattern.compile("(\\d+(?:\\.\\d+))");
      Matcher m = p.matcher(deltaSatResult);
      double delta = Double.NaN;
      if(m.find())
        delta = Double.parseDouble(m.group(1));
      return delta;
    }

    private double getDoubleFromStr(String d) {
      if(d.equals("-INFTY"))
        return Double.NEGATIVE_INFINITY;
      else if(d.equals("INFTY"))
        return Double.POSITIVE_INFINITY;
      else
        return Double.parseDouble(d);
    }
  }
}
