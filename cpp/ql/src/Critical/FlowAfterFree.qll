import cpp
import semmle.code.cpp.dataflow.new.DataFlow

/** Signature for a predicate that holds for a dataflow node and an expression whichs holds if the sink is the sought target */
signature predicate sink(DataFlow::Node dfe, Expr e);

/**
 * Parameterized module to find flow between
 *  an deallocation and the given target
 *
 *  The sink must either be post dominiating a free or dominated by a free.
 */
module FlowFromFree<sink/2 targetExpr> {
  /**
   * Holds if `n` is a dataflow node that is reachable from the
   * argument of a `DeallocationExpr` that is free'ing the
   * expression `e`.
   */
  private predicate flowsFrom(DataFlow::Node n, Expr e) {
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
  private predicate sanitizes(DataFlow::Node n) {
    n.asIndirectExpr() = any(AddressOfExpr aoe) or
    callByReference(_, n.asIndirectExpr().(VariableAccess).getTarget())
  }

  /**
   * Holds if `n` is a dataflow node that is part of a path
   * from one `Expr e1` to another `Expr e2`
   * such that one of the following two conditions hold:
   * 1. `e1` dominates `e2`, or
   * 2. `e2` post-dominates `e1`.
   */
  private predicate flowsTo(DataFlow::Node n) {
    exists(Expr source | flowsFrom(n, source) |
      exists(Expr sink | targetExpr(n, sink) |
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
   */
  predicate step(DataFlow::Node n1, DataFlow::Node n2) {
    flowsTo(n1) and
    flowsTo(n2) and
    DataFlow::localFlowStep(n1, n2)
  }

  predicate flows(DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2) {
    freeExpr(dfe1, e1) and
    targetExpr(dfe2, e2) and
    e1 != e2 and
    step+(dfe1, dfe2) and
    (
      dominates(e1, e2) or
      postDominates(e2, e1)
    )
  }
}

/** Holds if `dfe` is an deallocation. */
predicate freeExpr(DataFlow::Node dfe, Expr e) {
  //e = any(DeallocationExpr de).getFreedExpr() and
  e = Dealloc::getIndirectFreedExpr() and
  e = dfe.asExpr() and
  not e = any(PointerDereferenceExpr pde)
}

private module Dealloc {
  private predicate sourceExpr(DataFlow::Node n, Expr e) {
    exists(Function f, Parameter p |
      p = f.getAParameter() and
      n.asParameter() = p and
      e.getBasicBlock() = f.getEntryPoint().getBasicBlock()
    )
  }

  private predicate sinkExpr(DataFlow::Node n, Expr e) {
    e = getIndirectFreedExpr() and
    n.asExpr() = e
  }

  private predicate sanitizeExpr(DataFlow::Node n) {
    n.asIndirectExpr() = any(AddressOfExpr aoe) or
    callByReference(_, n.asIndirectExpr().(VariableAccess).getTarget())
  }

  /**
   * Holds if `n` is a dataflow node that is reachable from the
   * argument of `sourceExpr` that reaches `sinkExpr`
   */
  private predicate flowsFrom(DataFlow::Node n, Expr e) {
    sourceExpr(n, e)
    or
    exists(DataFlow::Node prev |
      flowsFrom(prev, e) and
      DataFlow::localFlowStep(prev, n) and
      not sanitizeExpr(n)
    )
  }

  /**
   * Holds if `n` is a dataflow node that is part of a path
   * from one `Expr e1` to another `Expr e2`
   * such that `flowStep(e1, e2)` holds.
   */
  private predicate flowsTo(DataFlow::Node n) {
    exists(Expr source | flowsFrom(n, source) |
      exists(Expr sink | sinkExpr(n, sink) | postDominates(sink, source))
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
   * of a path from one `DeallocationExpr` to the target expression.
   */
  private predicate step(DataFlow::Node n1, DataFlow::Node n2) {
    flowsTo(n1) and
    flowsTo(n2) and
    DataFlow::localFlowStep(n1, n2)
  }

  private predicate flows(DataFlow::Node dfe1, DataFlow::Node dfe2, Expr e1, Expr e2) {
    step+(dfe1, dfe2) and
    postDominates(e2, e1)
  }

  private predicate isDeallocFunction(Function f, int index) {
    exists(DataFlow::ParameterNode source, DataFlow::Node sink |
      source.asParameter() = f.getParameter(index) and
      // deallocExpr.getEnclosingVariable() = source.asParameter() and
      sink.asExpr() = getIndirectFreedExpr()
    |
      // This flow should be augmented to sanitize the flow.
      //DataFlow::localFlow(source, sink) and
      //postDominates(sink.asExpr(), f.getEntryPoint())
      exists(Expr sourceExpr, Expr sinkExpr |
        flows(source, sink, sourceExpr, sinkExpr) and
        postDominates(sinkExpr, sourceExpr)
      )
      // There is no flow here!!
    )
  }

  Expr getIndirectFreedExpr() {
    result = any(DeallocationExpr de).getFreedExpr() and
    not exists(DeallocationFunction df | df.getACallToThisFunction().getAChild() = result |
      df.getName().matches("%realloc") or
      df.hasName("MmFreePagesFromMdl")
    )
    or
    exists(FunctionCall fc, Function f, int index |
      fc.getArgument(index) = result and
      fc.getTarget() = f and
      isDeallocFunction(fc.getTarget(), index)
    )
  }
}
