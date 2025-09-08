/**
 * @kind path-problem
 * @id c/uninit
 * @problem.severity warning
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking

module MyConf implements DataFlow::ConfigSig {

  int fieldFlowBranchLimit() { result = 100000 }

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

    // For some reason, using `FunctionCall` does not work. Use `Function` instead.

    exists(Function fn |
      (
        fn.getName() = "memcpy" or
        fn.getName() = "memset" or
        fn.getName() = "memmove" or
        fn.getName().regexpMatch(".*copy_from_user") or
        fn.getName().regexpMatch(".*memcpy")
      )
      and (
        // src or length arguments
        fn.getParameter(1) = node.asParameter() or
        fn.getParameter(2) = node.asParameter()
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

    exists(GuardCondition gc, Variable v |
      gc.getAChild*() = v.getAnAccess() and
      node.asExpr() = v.getAnAccess() and
      gc.controls(node.asExpr().getBasicBlock(), _) and
      not exists(Loop loop | loop.getControllingExpr() = gc)
    )
    or exists(FunctionCall fc |
      fc.getAnArgument() = node.asIndirectArgument()
      and node.asIndirectArgument() instanceof AddressOfExpr
    )
    or exists(StoreInstruction si |
      si = node.asInstruction()
    )
  }
}

module Flow = TaintTracking::Global<MyConf>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink) and source.getLocation() != sink.getLocation()
select sink.getNode(), source, sink, "Sink is reached from $@.", source.getNode(), "here"