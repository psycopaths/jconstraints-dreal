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

import java.util.Properties;
import java.util.logging.Logger;

import junit.framework.Assert;
import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.api.ConstraintSolver.Result;
import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Valuation;
import gov.nasa.jpf.constraints.api.ValuationEntry;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverFactory;

public class TstUtil {

  private static final Logger log = Logger.getLogger(TstUtil.class.getName());
  
	public static final boolean PRINT_DREAL_EXPR = true;
	
	public static DrealSolver createDrealSolver(Properties conf) {
		conf.setProperty("symbolic.dp", "dreal");
		conf.setProperty("dreal.path", "/Users/luckow/programs/dreal/bin/dReal");
		ConstraintSolverFactory factory = new ConstraintSolverFactory(conf);
		ConstraintSolver solver = factory.createSolver();
		return (DrealSolver) solver;
	}
	
	public static Valuation runTest(ConstraintSolver solver, Expression<Boolean> expr, Result expectedRes, boolean printCoralExpr) {
	  log.info("Expr: " + expr.toString());
		try {
			if(printCoralExpr) {
				DrealExpressionGenerator expGen = new DrealExpressionGenerator();
				String constraint = expGen.generateAssertion(expr);
				log.info("dReal Expr: " + constraint.toString());
			}
			Valuation val = new Valuation();
			long start = System.currentTimeMillis();
	        Result res = solver.solve(expr, val);
	        long solverTime = (System.currentTimeMillis() - start);
	        log.info("Solver time: " + solverTime + "ms");
	        log.info("Expected " + expectedRes + " got " + res);
	        if(res == Result.SAT) {
	          log.info("-------Valuation-------");
		        for(ValuationEntry<?> exp : val)
		          log.info(exp.getVariable() + "=" + exp.getValue());
		        log.info("-----------------------");
	        }
	        Assert.assertEquals(expectedRes, res);
	        return val;
		} catch(Exception e) {
			throw e;
		} finally {
		  log.info("======================================================================");
		}
	}

}
