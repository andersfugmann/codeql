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
import FlowAfterFree as Flow

module DoubleFreeFlow = Flow::FlowFromFree<Flow::freeExpr/2>;

query predicate edges = DoubleFreeFlow::step/2;

from DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2
where DoubleFreeFlow::flows(dfe1, dfe2, e1, e2)
select e2, dfe1, dfe2, "Potential Double free of '" + e1.toString() + "' may have $@.", e1,
  "been previously freed"
