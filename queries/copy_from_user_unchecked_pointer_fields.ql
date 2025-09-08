/**
 * @kind path-problem
 * @id c/uninit
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.controlflow.Guards
module CopyFromUserStructPtrConfig implements DataFlow::ConfigSig {

  /** Source: the struct memory copied from user */
  predicate isSource(DataFlow::Node node) {
    exists(FunctionCall fc |
      fc.getTarget().hasGlobalName("copy_from_user") and
      fc.getArgument(0) = node.asIndirectArgument()
    )
  }

  /** Sink: pointer-typed field of that struct */
  predicate isSink(DataFlow::Node node) {
    node.asExpr() instanceof FieldAccess and
    node.asExpr().getType() instanceof PointerType
  }

  /**
   * Only propagate taint **from the struct itself to its fields**.
   * Do NOT propagate through array indexing or other derived structs.
   */
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(FieldAccess fa |
      pred.asExpr() = fa.getQualifier() and
      succ.asExpr() = fa and
      fa.getType() instanceof PointerType
    )
  }

  /** Barrier: NULL checks */
  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition gc, Variable v |
      gc.controls(node.asExpr().getBasicBlock(), _) and
      node.asExpr() = v.getAnAccess() and
      gc.getAChild*() = v.getAnAccess() and
      (
        exists(Literal lit | gc.getAChild*() = lit and (lit.toString() = "0" or lit.toString() = "NULL"))
        or gc.toString() = v.getAnAccess().toString()
        or exists(Expr notExpr | notExpr = gc.getAChild() and
                                    notExpr.toString().regexpMatch("^!\\s*.*") and
                                    notExpr.getAChild*() = v.getAnAccess())
      )
      and not exists(Loop loop | loop.getControllingExpr() = gc)
    )
  }
}


module Flow = TaintTracking::Global<CopyFromUserStructPtrConfig>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"