/**
 * @kind path-problem
 * @id c/test-path-problem2
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking

module MyConf implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {
    node.asExpr().(FunctionCall).getTarget().hasGlobalName("strlen") or
    node.asExpr().(FunctionCall).getTarget().hasGlobalName("ntoh") or
    exists(FunctionCall fc |
      fc.getTarget().getName().regexpMatch("copy_from_user") and
      fc.getArgument(0) = node.asIndirectArgument()
    )
  }

  predicate isSink(DataFlow::Node node) {
    exists(ArrayExpr ae | node.asExpr() = ae.getArrayOffset())
  }

  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(Loop loop, LoopCounter lc |
      loop = lc.getALoop() and
      loop.getControllingExpr().(RelationalOperation).getGreaterOperand() = pred.asExpr()
    |
      succ.asExpr() = lc.getVariableAccessInLoop(loop)
    )
  }

  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition gc, Variable v |
      gc.getAChild*() = v.getAnAccess() and
      node.asExpr() = v.getAnAccess() and
      gc.controls(node.asExpr().getBasicBlock(), _) and
      not exists(Loop loop | loop.getControllingExpr() = gc)
    )
  }
}

module Flow = TaintTracking::Global<MyConf>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"