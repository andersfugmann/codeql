// generated by codegen, remove this comment if you wish to edit this file
/**
 * This module provides a hand-modifiable wrapper around the generated class `TupleStructPat`.
 */

private import codeql.rust.generated.TupleStructPat

/**
 * A tuple struct pattern. For example:
 * ```
 * match x {
 *     Tuple("a", 1, 2, 3) => "great",
 *     Tuple(.., 3) => "fine",
 *     Tuple(..) => "fail",
 * };
 * ```
 */
class TupleStructPat extends Generated::TupleStructPat { }
