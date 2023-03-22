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
  e = dfe.asExpr() and
  // Ignore any function named realloc
  exists(DeallocationFunction df | df.getACallToThisFunction().getAChild() = e |
    not df.getName().regexpMatch(".*realloc") and
    not df.hasName("MmFreePagesFromMdl") and
    // Ignore free on pointer dereferences
    not e = any(PointerDereferenceExpr pde)
  )
}

/**
 * Holds if `n` is a dataflow node that is reachable from the
 * argument of a `DeallocationExpr` that is free'ing the
 * expression `e`.
 */
predicate flowsFrom(DataFlow::Node n, Expr e) {
  freeExpr(n, e)
  or
  exists(DataFlow::Node prev |
    flowsFrom(prev, e) and
    DataFlow::localFlowStep(prev, n) and
    not sanitizes(n)
  )
}

/**
 * Holds if the address of the dataflow node `n` passed to a function call
 * or if `n` is passed as a references in a function call such that the
 * memory pointed to by `n` may be changed by the function call.
 */
predicate sanitizes(DataFlow::Node n) {
  n.asIndirectExpr() = any(AddressOfExpr aoe)
  or
  exists(Call c, int i | c.getArgument(i) = n.asIndirectExpr() |
    c.getTarget().getParameter(i).getType() instanceof ReferenceType
  )
}

/**
 * Holds if `n` is a dataflow node that is part of a path
 * from one `Expr e1` to another `Expr e2`
 * such that one of the following two conditions hold:
 * 1. `e1` dominates `e2`, or
 * 2. `e2` post-dominates `e1`.
 */
predicate flowsTo(DataFlow::Node n) {
  exists(Expr source | flowsFrom(n, source) |
    exists(Expr sink | freeExpr(n, sink) |
      dominates(source, sink) or
      postDominates(sink, source)
    )
    or
    exists(DataFlow::Node succ |
      flowsTo(succ) and
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
  flowsTo(n1) and
  flowsTo(n2) and
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
    dominates(e1, e2) or
    postDominates(e2, e1)
  )
select e2, dfe1, dfe2, "Potential Double free of '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
