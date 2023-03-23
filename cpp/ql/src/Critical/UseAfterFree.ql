/**
 * @name Potential use after free
 * @description An allocated memory block is used after it has been freed. Behavior in such cases is undefined and can cause memory corruption.
 * @kind path-problem
 * @id cpp/use-after-free
 * @problem.severity warning
 * @security-severity 9.3
 * @tags reliability
 *       security
 *       external/cwe/cwe-416
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow
import FlowAfterFree as Flow

module UseAfterFreeFlow = Flow::FlowFromFree<useExpr/2>;

predicate useExpr(DataFlow::Node dfe, Expr e) {
  e = dfe.asExpr() and
  (
    e = any(ReturnStmt rs).getExpr() or
    e = any(FunctionCall fc).getAChild() or
    e = any(PointerDereferenceExpr pde).getOperand() or
    e = any(PointerFieldAccess pfa).getQualifier() or
    e = any(ArrayExpr ae).getArrayBase()
  ) and
  not Flow::freeExpr(dfe, e)
}

query predicate edges = UseAfterFreeFlow::step/2;

from DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2
where UseAfterFreeFlow::flows(dfe1, dfe2, e1, e2)
select e2, dfe1, dfe2, "Memory pointed to by '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
