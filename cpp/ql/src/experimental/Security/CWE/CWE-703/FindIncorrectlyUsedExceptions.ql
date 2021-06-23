/**
 * @name Operator Find Incorrectly Used Exceptions
 * @description --Finding places for the dangerous use of exceptions.
 * @kind problem
 * @id cpp/operator-find-incorrectly-used-exceptions
 * @problem.severity warning
 * @precision medium
 * @tags correctness
 *       security
 *       external/cwe/cwe-703
 *       external/cwe/cwe-248
 *       external/cwe/cwe-390
 */

import cpp

from FunctionCall fc, string msg
where
  exists(ThrowExpr texp |
    texp.getEnclosingFunction() = fc.getTarget() and
    (
      fc.getTarget().hasGlobalOrStdName("DllMain") and
      not exists(TryStmt ts |
        texp.getEnclosingStmt().getParentStmt*() = ts.getStmt() and
        not ts.getACatchClause().isEmpty()
      ) and
      msg = "DllMain contains exeption no wrapped to try..catch blocks."
      or
      texp.getExpr().isParenthesised() and
      texp.getExpr().(CommaExpr).getLeftOperand().isConstant() and
      texp.getExpr().(CommaExpr).getRightOperand().isConstant() and
      msg = "There is an exception in the function that requires your attention."
    )
  )
  or
  fc.getTarget() instanceof Constructor and
  fc.getTargetType().(Class).getABaseClass+().hasGlobalOrStdName("exception") and
  not fc.isInMacroExpansion() and
  not exists(ThrowExpr texp | fc.getEnclosingStmt() = texp.getEnclosingStmt()) and
  not exists(FunctionCall fctmp | fctmp.getAnArgument() = fc) and
  not fc instanceof ConstructorDirectInit and
  not fc.getEnclosingStmt() instanceof DeclStmt and
  not fc instanceof ConstructorDelegationInit and
  msg = "This object does not generate an exception."
select fc, msg
