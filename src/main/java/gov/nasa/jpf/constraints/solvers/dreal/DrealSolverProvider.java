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

import gov.nasa.jpf.constraints.api.ConstraintSolver;
import gov.nasa.jpf.constraints.solvers.ConstraintSolverProvider;
import gov.nasa.jpf.constraints.solvers.dreal.DrealSolver.DrealSolverBuilder;

public class DrealSolverProvider implements ConstraintSolverProvider {

	@Override
	public String[] getNames() {
		return new String[]{"dreal"};
	}

	@Override
	public ConstraintSolver createSolver(Properties props) {
	  DrealSolverBuilder solverbuilder = new DrealSolverBuilder();
		try {
			if(props.containsKey(DrealConfig.SOLVER_PATH.getPropStr()))
				solverbuilder.setDrealPath(props.getProperty(DrealConfig.SOLVER_PATH.getPropStr()));
			if(props.containsKey(DrealConfig.SOLVER_PATH.getPropStr()))
        solverbuilder.setDrealPath(props.getProperty(DrealConfig.SOLVER_PATH.getPropStr()));
		} catch(Exception e) {
			throw new DrealSolverException("Invalid configuration of dReal.", e);
		}
		return solverbuilder.build();
	}
}
