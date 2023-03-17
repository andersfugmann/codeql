/**
 * @name Potential double free
 * @description An allocated memory block is free multiple times. Behavior in such cases is undefined and can cause memory corruption.
 * @kind path-problem
 * @id cpp/double-free
 * @problem.severity warning
 * @security-severity 9.3
 * @tags reliability
 *       security
 *       external/cwe/cwe-415
 */

import cpp
import semmle.code.cpp.dataflow.new.DataFlow

predicate freeExpr(DataFlow::Node dfe, Expr e) {
  e = any(DeallocationExpr de).getFreedExpr() and
  e = dfe.asExpr()
}

/**
 * Holds if `n` is a dataflow node that is reachable from the
 * argument of a `DeallocationExpr` that is free'ing the
 * expression `e`.
 */
predicate flowsFromFree(DataFlow::Node n, Expr e) {
  freeExpr(n, e)
  or
  exists(DataFlow::Node prev |
    flowsFromFree(prev, e) and
    DataFlow::localFlowStep(prev, n)
  )
}

/**
 * Holds if `n` is a dataflow node that is part of a path
 * from one `DeallocationExpr de1` to another `DeallocationExpr de2`
 * such that one of the following two conditions hold:
 * 1. `de1` dominates `de2`, or
 * 2. `de2` post-dominates `de1`.
 */
predicate flowsToFree(DataFlow::Node n) {
  exists(Expr source | flowsFromFree(n, source) |
    exists(Expr sink | freeExpr(n, sink) |
      dominates(source, sink) or
      postDominates(sink, source)
    )
    or
    exists(DataFlow::Node succ |
      flowsToFree(succ) and
      DataFlow::localFlowStep(n, succ)
    )
  )
}

/**
 * Holds if `n1` steps to `n2` in one local flow step.
 *
 * This predicate is restricted to the steps that are part
 * of a path from one `DeallocationExpr` to another.
 */
predicate step(DataFlow::Node n1, DataFlow::Node n2) {
  flowsToFree(n1) and
  flowsToFree(n2) and
  DataFlow::localFlowStep(n1, n2)
}

query predicate edges = step/2;

from DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2
where
  freeExpr(dfe1, e1) and
  freeExpr(dfe2, e2) and
  e1 != e2 and
  step+(dfe1, dfe2) and
  (
    bbDominates(e1.getBasicBlock(), e2.getBasicBlock()) or
    bbPostDominates(e2.getBasicBlock(), e1.getBasicBlock())
  ) and
  (
    dominates(e1, e2) or
    postDominates(e2, e1)
  )
select e2, dfe1, dfe2, "Potential Double free of '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
