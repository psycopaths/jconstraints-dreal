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

import java.util.List;

import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;

public class DrealResult {
  
  private final Result result;
  private List<DrealValuationResult> valuations;
  private double delta = -1;
  
  public DrealResult(Result result) {
    this.result = result;
  }
  
  public DrealResult(Result result, List<DrealValuationResult> valuations, double delta) {
    this.result = result;
    this.valuations = valuations;
    this.delta = delta;
  }

  public List<DrealValuationResult> getValuations() {
    return this.valuations;
  }
  
  public double getDelta() {
	  return this.delta;
  }
  
  public DrealValuationResult getValuation(String variableName) {
    for(DrealValuationResult var : this.valuations) {
      if(var.getVariableName().equals(variableName))
        return var;
    }
    return null;
  }
  
  public Result getResult() {
    return this.result;
  }
}
