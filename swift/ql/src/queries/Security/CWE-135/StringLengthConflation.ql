/**
 * @name String length conflation
 * @description TODO
 * @kind problem
 * @problem.severity TODO
 * @security-severity TODO
 * @precision TODO
 * @id swift/string-length-conflation
 * @tags security
 *       external/cwe/cwe-135
 */

import swift
import codeql.swift.dataflow.DataFlow
import DataFlow::PathGraph

class StringLengthConflationConfiguration extends DataFlow::Configuration {
  StringLengthConflationConfiguration() { this = "StringLengthConflationConfiguration" }

  override predicate isSource(DataFlow::Node node, string flowstate) {
    // result of a call to to `String.count`
    exists(MemberRefExpr member |
      member.getBaseExpr().getType().toString() = "String" and // TODO: use of toString
      member.getMember().toString() = "count" and // TODO: use of toString
      node.asExpr() = member and
      flowstate = "String"
    )
  }

  override predicate isSink(DataFlow::Node node, string flowstate) {
    // arguments to method calls...
    exists(
      string className, string methodName, string argName, ClassDecl c, AbstractFunctionDecl f,
      CallExpr call, int arg
    |
      (
        // `NSRange.init`
        className = "NSRange" and
        methodName = "init" and
        argName = ["location", "length"]
        or
        // `NSString.character`
        className = ["NSString", "NSMutableString"] and
        methodName = "character" and
        argName = "at"
        or
        // `NSString.character`
        className = ["NSString", "NSMutableString"] and
        methodName = "substring" and
        argName = ["from", "to"]
        or
        // `NSMutableString.insert`
        className = "NSMutableString" and
        methodName = "insert" and
        argName = "at"
      ) and
      c.toString() = className and // TODO: use of toString
      c.getAMember() = f and // TODO: will this even work if its defined in a parent class?
      call.getFunction().(ApplyExpr).getFunction().(DeclRefExpr).getDecl() = f and
      call.getFunction().(ApplyExpr).getFunction().toString() = methodName and // TODO: use of toString
      call.getFunction()
          .(ApplyExpr)
          .getFunction()
          .(DeclRefExpr)
          .getDecl()
          .(AbstractFunctionDecl)
          .getParam(arg)
          .getName() = argName and
      call.getArgument(arg).getExpr() = node.asExpr() and
      flowstate = "String" // `String` length flowing into `NSString`
    )
    or
    // arguments to function calls...
    exists(string funcName, string argName, CallExpr call, int arg |
      // `NSMakeRange`
      funcName = "NSMakeRange" and
      argName = ["loc", "len"] and
      call.getStaticTarget().getName().matches(funcName + "%") and
      call.getStaticTarget().getParam(arg).getName() = argName and
      call.getArgument(arg).getExpr() = node.asExpr() and
      flowstate = "String" // `String` length flowing into `NSString`
    )
  }
}

from StringLengthConflationConfiguration config, DataFlow::PathNode source, DataFlow::PathNode sink
where config.hasFlowPath(source, sink)
select sink, source, sink, "RESULT"
