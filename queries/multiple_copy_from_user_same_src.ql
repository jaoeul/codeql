/**
 * @kind path-problem
 * @id c/uninit
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking

module MultipleCopyFromUserSameSrcConfiguration implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {

    exists(FunctionCall fc |
      fc.getTarget().getName().regexpMatch(".*copy_from_user")
      and
      fc.getArgument(1) = node.asIndirectArgument()
    )
  }

    predicate isSink(DataFlow::Node node) {
      exists(FunctionCall fc |
        fc.getTarget().getName().regexpMatch("copy_from_user")
        and
        fc.getArgument(1) = node.asIndirectArgument()
      )
  }

  //predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
  //  isSource(pred) and isSink(succ) and
  //  pred.asExpr().(FunctionCall).getTarget().hasGlobalName("strlen") and
  //  exists(FunctionCall fc |
  //    fc.getTarget().getName().regexpMatch("strcpy") and
  //    fc.getArgument(0) = succ.asIndirectArgument()
  //  )
  //}

  //predicate isBarrier(DataFlow::Node node) {
  //  exists(GuardCondition gc, Variable v |
  //    gc.getAChild*() = v.getAnAccess() and
  //    node.asExpr() = v.getAnAccess() and
  //    gc.controls(node.asExpr().getBasicBlock(), _) and
  //    not exists(Loop loop | loop.getControllingExpr() = gc)
  //  )
  //}
}

module Flow = TaintTracking::Global<MultipleCopyFromUserSameSrcConfiguration>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"