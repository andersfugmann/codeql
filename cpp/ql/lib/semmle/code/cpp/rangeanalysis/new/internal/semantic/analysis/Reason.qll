/**
 * Provides a `Make` parameterized module for constructing a `Reason` type that is used
 * when implementing the `LangSig` module.
 */

private import semmle.code.cpp.rangeanalysis.new.internal.semantic.Semantic

/** The necessary parameters that must be implemented to instantiate `Make`. */
signature module ParamSig {
  class TypeReasonImpl;
}

/**
 * The module that constructs a `Reason` type when provided with an implementation
 * of `ParamSig`.
 */
module Make<ParamSig Param> {
  private import Param

  private newtype TSemReason =
    TSemNoReason() or
    TSemCondReason(SemGuard guard) or
    TSemTypeReason(TypeReasonImpl trc)

  /**
   * A reason for an inferred bound. This can either be `CondReason` if the bound
   * is due to a specific condition, or `NoReason` if the bound is inferred
   * without going through a bounding condition.
   */
  abstract class SemReason extends TSemReason {
    /** Gets a textual representation of this reason. */
    abstract string toString();

    bindingset[this, reason]
    abstract SemReason combineWith(SemReason reason);
  }

  /**
   * A reason for an inferred bound that indicates that the bound is inferred
   * without going through a bounding condition.
   */
  class SemNoReason extends SemReason, TSemNoReason {
    override string toString() { result = "NoReason" }

    override SemReason combineWith(SemReason reason) { result = reason }
  }

  /** A reason for an inferred bound pointing to a condition. */
  class SemCondReason extends SemReason, TSemCondReason {
    /** Gets the condition that is the reason for the bound. */
    SemGuard getCond() { this = TSemCondReason(result) }

    override string toString() { result = this.getCond().toString() }

    bindingset[this, reason]
    override SemReason combineWith(SemReason reason) {
      if reason instanceof SemTypeReason then result instanceof SemTypeReason else result = this
    }
  }

  /**
   * A reason for an inferred bound that indicates that the bound is inferred
   * based on type-information.
   */
  class SemTypeReason extends SemReason, TSemTypeReason {
    TypeReasonImpl impl;

    SemTypeReason() { this = TSemTypeReason(impl) }

    override string toString() { result = "TypeReason" }

    bindingset[this, reason]
    override SemReason combineWith(SemReason reason) { result = this and exists(reason) }
  }
}
