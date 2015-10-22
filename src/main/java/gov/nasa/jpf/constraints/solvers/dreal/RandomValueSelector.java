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

import java.util.Random;

import gov.nasa.jpf.constraints.solvers.dreal.DrealValuationResult.Interval;

public class RandomValueSelector implements ValueSelector {
  
  private Random rgen;
  
  public RandomValueSelector() {
    rgen = new Random(); 
  }
  
  public RandomValueSelector(int seed) {
    rgen = new Random(seed);
  }
  
  @Override
  public double getValue(Interval val) {
    double min, max;
    if(Double.isInfinite(val.start))
      min = Double.MIN_VALUE;
    else
      min = val.start;
    
    if(Double.isInfinite(val.end))
      max = Double.MAX_VALUE;
    else
      max = val.end;      
    
    return min + (max - min) * rgen.nextDouble();
  }
}
