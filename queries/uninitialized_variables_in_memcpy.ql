/**
 * @kind path-problem
 * @id c/test-path-problem2
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking

module MyConf implements DataFlow::ConfigSig {

  int fieldFlowBranchLimit() { result = 10000 }

  // Removes a level of indirection. E.g. `char*`->`char` or `char**`->`char*`
  additional Type deref(Type t) { result = t.(DerivedType).getBaseType() }

// Removes all indirection levels. E.g. `char*`->`char` or `char*****`->`char`
  additional Type max_deref(Type t) {
    t.getPointerIndirectionLevel() = 0 and result = t
    or
    t.getPointerIndirectionLevel() > 0 and result = max_deref(deref(t))
  }

  additional predicate allocatedType(Type t) {
    /* Arrays: "int foo[1]; foo[0] = 42;" is ok. */
    t instanceof ArrayType
    or
    /* Structs: "struct foo bar; bar.baz = 42" is ok. */
    t instanceof Class
    or
    /* Typedefs to other allocated types are fine. */
    allocatedType(t.(TypedefType).getUnderlyingType())
    or
    /* Type specifiers don't affect whether or not a type is allocated. */
    allocatedType(t.getUnspecifiedType())
  }

  predicate isSource(DataFlow::Node node) {
    node.asInstruction() instanceof UninitializedInstruction and
    exists(Type t | t = node.asInstruction().getResultType() | not allocatedType(t))
  }

  predicate isSink(DataFlow::Node node) {
    exists(
      FunctionCall fc |
        (
          //fc.getTarget().getName().regexpMatch("memmove")) and
          fc.getTarget().getName().regexpMatch("memcpy") and
        (
          //fc.getArgument(1) = node.asIndirectArgument() or 
          fc.getArgument(1) = node.asIndirectArgument()
        )
      )
    )
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
    // Remove "=" assignments from flow.
    exists(AssignExpr ae, Variable v, StoreInstruction si |
      (
        //ae.getLValue() = node.asExpr().(Assignment).getLValue() and
        //ae = node.asExpr().(Assignment) and
        v.getAnAssignment() = node.asExpr()
      )
      or
      (
        v.getAnAssignment() = node.(DataFlow::PostUpdateNode).asExpr()
      )
      or
      (
        si = node.asInstruction()
      )
      or
      (
        si = node.(DataFlow::PostUpdateNode).asInstruction()
      )
      //and
      //(
      //  ae.getLValue() = node.asExpr() or
      //  ae.getRValue() = node.asExpr()
      //)
    )
    //or
    //// Remove calls memcpy() where our target variable is the destination frow flow.
    //exists(FunctionCall fc |
    //  fc.getTarget().getName().regexpMatch("memcpy") and
    //  fc.getArgument(0) = node.asIndirectArgument()
    //)
  }
}

module Flow = TaintTracking::Global<MyConf>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"