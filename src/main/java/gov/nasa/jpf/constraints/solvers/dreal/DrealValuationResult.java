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

public class DrealValuationResult {
  public static class Interval {
    double start;
    double end;
    
    public Interval(double start, double end) {
      this.start = start;
      this.end = end;
    }
    
    @Override
    public String toString() {
      return "[" + start + ", " + end + "]";
    }
  }
  
  private final Interval valuation;
  private final String variable;
  
  public DrealValuationResult(String variable, double intervalStart, double intervalEnd) {
    this.valuation = new Interval(intervalStart, intervalEnd);
    this.variable = variable;
  }

  public String getVariableName() {
    return variable;
  }

  public Interval getValuation() {
    return valuation;
  }
  
  @Override
  public String toString() {
    return variable + " : " + this.valuation.toString();
  }
}
