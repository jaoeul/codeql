/**
 * @kind path-problem
 * @id c/uninit
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.controlflow.Guards

module MultipleCopyFromUserSameSrcConfiguration implements DataFlow::ConfigSig {
  predicate isSource(DataFlow::Node node) {

    exists(FunctionCall fc |
      fc.getTarget().getName().regexpMatch(".*copy_from_user")
      and
      fc.getArgument(0) = node.asIndirectArgument()
    )
  }

    predicate isSink(DataFlow::Node node) {
      dereferenced(node.asExpr())
  }

  //predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
  //  isSource(pred) and isSink(succ) and
  //  pred.asExpr().(FunctionCall).getTarget().hasGlobalName("strlen") and
  //  exists(FunctionCall fc |
  //    fc.getTarget().getName().regexpMatch("strcpy") and
  //    fc.getArgument(0) = succ.asIndirectArgument()
  //  )
  //}

  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition gc, Variable v |
      // The guard dominates the dereference location
      gc.controls(node.asExpr().getBasicBlock(), _) and

      // We are dereferencing/accessing this variable
      node.asExpr() = v.getAnAccess() and

      // The guard *mentions* the same variable (covers: if (ptr), if (!ptr), if (ptr == 0/NULL), etc.)
      gc.getAChild*() = v.getAnAccess() and

      // Heuristic: prefer guards that look like (ptr == 0/NULL) or (ptr != 0/NULL),
      // but also allow implicit checks like if(ptr) / if(!ptr).
      (
        // explicit null/nonnull: ... == 0/NULL or ... != 0/NULL
        exists(Expr nullLike |
          gc.getAChild*() = nullLike and
          (
            nullLike.toString() = "0" or
            nullLike.toString() = "NULL"
          )
        )
        or
        // implicit non-null: if (ptr)
        gc.toString() = v.getAnAccess().toString()
        or
        // implicit null: if (!ptr)
        exists(Expr notExpr |
          notExpr = gc.getAChild() and
          notExpr.toString().regexpMatch("^!\\s*.*") and
          notExpr.getAChild*() = v.getAnAccess()
        )
      )

      // Avoid treating loop headers as barriers (keeps paths through loops visible)
      and not exists(Loop loop | loop.getControllingExpr() = gc)
    )
  }
}

module Flow = TaintTracking::Global<MultipleCopyFromUserSameSrcConfiguration>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"