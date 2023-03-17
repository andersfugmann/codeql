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

predicate freeExpr(DataFlow::Node dfe, Expr e) {
  dfe.asExpr() = any(DeallocationExpr de).getFreedExpr() and
  e = dfe.asExpr()
}

query predicate edges(DataFlow::Node dfe1, DataFlow::Node dfe2) {
  DataFlow::localFlowStep(dfe1, dfe2)
}

from DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2
where
  freeExpr(dfe1, e1) and
  dfe2.asExpr() = e2 and
  e1 != e2 and
  not freeExpr(dfe2, e2) and
  DataFlow::localFlow(dfe1, dfe2) and
  (
    bbDominates(e1.getBasicBlock(), e2.getBasicBlock()) or
    bbPostDominates(e2.getBasicBlock(), e1.getBasicBlock())
  ) and
  (
    dominates(e1, e2) or
    postDominates(e2, e1)
  )
//select e2, dfe1, dfe2, "Potential double free of $@.", e2, e2.toString()
select e2, dfe1, dfe2, "Memory pointed to by '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
