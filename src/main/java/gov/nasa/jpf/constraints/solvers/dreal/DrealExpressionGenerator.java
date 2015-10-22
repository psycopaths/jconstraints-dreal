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

import java.util.HashMap;
import java.util.List;

import gov.nasa.jpf.constraints.api.Expression;
import gov.nasa.jpf.constraints.api.Variable;
import gov.nasa.jpf.constraints.expressions.AbstractExpressionVisitor;
import gov.nasa.jpf.constraints.expressions.Constant;
import gov.nasa.jpf.constraints.expressions.Negation;
import gov.nasa.jpf.constraints.expressions.NumericBooleanExpression;
import gov.nasa.jpf.constraints.expressions.NumericComparator;
import gov.nasa.jpf.constraints.expressions.NumericCompound;
import gov.nasa.jpf.constraints.expressions.NumericOperator;
import gov.nasa.jpf.constraints.expressions.PropositionalCompound;
import gov.nasa.jpf.constraints.expressions.UnaryMinus;
import gov.nasa.jpf.constraints.expressions.functions.Function;
import gov.nasa.jpf.constraints.expressions.functions.FunctionExpression;
import gov.nasa.jpf.constraints.expressions.functions.math.BooleanDoubleFunction;
import gov.nasa.jpf.constraints.types.BuiltinTypes.DoubleType;
import gov.nasa.jpf.constraints.types.IntegerType;
import gov.nasa.jpf.constraints.types.Type;
import gov.nasa.jpf.constraints.util.ExpressionClassifier;

public class DrealExpressionGenerator extends AbstractExpressionVisitor<String, StringBuilder> {
  
  //TODO: get rid of the StringBuilder... not used, but could "optimize" it a bit..
  //We don't need a map actually... just a list of strings is fine
  private HashMap<String, Variable<?>> intVars;

  private HashMap<String, Variable<?>> doubleVars;
  
  public HashMap<String, Variable<?>> getIntVars() {
    return intVars;
  }

  public HashMap<String, Variable<?>> getDoubleVars() {
    return doubleVars;
  }
  
  public String generateAssertion(Expression<Boolean> expression) {
    this.intVars = new HashMap<>();
    this.doubleVars = new HashMap<>();
    //TODO: we could also set precision (possibly make it a parameter
    //e.g. (set-info :precision 0.001)
    StringBuilder smtlibExp = new StringBuilder();
    List<Expression<Boolean>> conjuncts = ExpressionClassifier.splitToConjuncts(expression);
    
    for(Expression<Boolean> conjunct : conjuncts) {
      smtlibExp.append("(assert ");
      smtlibExp.append(visit(conjunct));
      smtlibExp.append(" )\n");
    }
    StringBuilder declarations = new StringBuilder();
    declarations.append("(set-logic QF_NRA)\n");
    for(String var : this.intVars.keySet())
      declarations.append("(declare-fun " + var + " () Int)\n");
    for(String var : this.doubleVars.keySet())
      declarations.append("(declare-fun " + var + " () Real)\n");

    StringBuilder smtlibspec = declarations.
                               append(smtlibExp).
                               append("(check-sat)\n(exit)\n");
    return smtlibspec.toString();
  }
  
  @Override
  public <E> String visit(Constant<E> c, StringBuilder data) {
    return c.getValue().toString();
  }
  
  @Override
  public String visit(Negation n, StringBuilder data) {
    return "( not " + visit(n.getNegated()) + " )";
  }
  
  @Override
  public <E> String visit(NumericBooleanExpression n, StringBuilder data) {
    String left = visit(n.getLeft(), data);
    String right = visit(n.getRight(), data);
    String cmpStr;
    NumericComparator cmp = n.getComparator();
    
    switch(cmp) {
    case EQ:
      cmpStr = "=";
      break;
    case NE:
      return "(not (= " + left + " " + right + "))";
    case GE:
      cmpStr = ">=";
      break;
    case GT:
      cmpStr = ">";
      break;
    case LE:
      cmpStr = "<=";
      break;
    case LT:
      cmpStr = "<";
      break;
      default:
        throw new UnsupportedOperationException("No support for cmp operator: " + cmp.toString());
    }
    return "(" + cmpStr + " " + left + " " + right + ")";
  }
  
  @Override
  public <E> String visit(NumericCompound<E> n, StringBuilder data) {
    String left = visit(n.getLeft(), data);
    String right = visit(n.getRight(), data);
    String opStr;
    NumericOperator op = n.getOperator();
    
    switch(op) {
    case PLUS:
      opStr = "+";
      break;
    case MINUS:
      opStr = "-";
      break;
    case MUL:
      opStr = "*";
      break;
    case DIV:
      opStr = "/";
      break;
    case REM: //Not supported yet
      default:
        throw new UnsupportedOperationException("No support for operator: " + op.toString());
    }
    return "(" + opStr + " " + left + " " + right + ")"; 
  }
  
  @Override
  public <E> String visit(UnaryMinus<E> n, StringBuilder data) {
    return "(* -1 " + visit(n.getNegated()) + " )";
  }

  @Override
  public <E> String visit(Variable<E> v, StringBuilder data) {
    Type<E> t = v.getType();
    if(t instanceof DoubleType) {
      if(!this.doubleVars.containsKey(v.getName()))
        this.doubleVars.put(v.getName(), v);
    } else if(t instanceof IntegerType) {
      if(!this.intVars.containsKey(v.getName()))
        this.intVars.put(v.getName(), v);
    }
    return v.getName();
  }
  
  @Override
  public <E> String visit(FunctionExpression<E> f, StringBuilder data) {
    String funcName = f.getFunction().getName();
    if(funcName.equals(BooleanDoubleFunction.DOUBLE_IS_NAN.getName()) ||
       funcName.equals(BooleanDoubleFunction.DOUBLE_IS_INFINITE.getName())) {
      return " false ";
    } else if(funcName.equals("java.lang.Double.doubleToLongBits")) {
      return visit(f.getArgs()[0]);
    }
    String args = visit(f.getArgs()[0]);
    if(funcName.equals("atan2") ||
        funcName.equals("pow")) {
      args += " " + visit(f.getArgs()[1]);
    }
    return "( " + funcName + " " + args + ")";
  }
  
  @Override
  public String visit(PropositionalCompound n, StringBuilder data) {
    String left = visit(n.getLeft(), data);
    String right = visit(n.getRight(), data);
    String opStr;
    switch(n.getOperator()) {
    case AND:
      opStr = "and";
      break;
    case OR:
      opStr = "or";
      break;
    case XOR:
    case EQUIV:
    case IMPLY:
    default:
      throw new IllegalStateException("Cannot handle logical operator " + n.getOperator());
    }
    return "(" + opStr + " " + left + " " + right + ")"; 
  }
}
