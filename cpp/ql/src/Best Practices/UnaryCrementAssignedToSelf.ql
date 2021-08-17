/**
 * @name Unspecified behaviour when using unary increment and assignent
 * @kind problem
 * @problem.severity recommendation
 * @precision high
 * @id cpp/unary-increment
 */

import cpp

from LocalVariable v, AssignExpr aae, VariableAccess va1, VariableAccess va2, PostfixCrementOperation co
where
    // Only postfix incrments seems to cause problems, and not i all cases.
    (aae.getLValue() = va1 and
     va1.getTarget() = v and
     aae.getRValue() = co and
     co.getOperand() = va2 and
     va2.getTarget() = v
    )
select aae, "Variable " + v.getName() + " has unspecified value after assigment, due to use of unary in/de-crement operator on right hand side"
