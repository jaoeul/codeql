/**
 * @kind path-problem
 * @id c/copy-from-user-struct-ptr
 * @problem.severity warning
 * @description Detects dereferences of pointer fields in structs copied from user space via copy_from_user without NULL checks
 * @tags security
 *       user-space
 *       null-dereference
 */

import cpp
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.dataflow.new.TaintTracking
import semmle.code.cpp.dataflow.new.DataFlow

module CopyFromUserStructPtrConfig implements DataFlow::ConfigSig {
  /**
   * Source: the struct memory copied from user space via copy_from_user.
   * Identifies the destination buffer of copy_from_user calls.
   */
  predicate isSource(DataFlow::Node node) {
    exists(FunctionCall call |
      call.getTarget().hasName("copy_from_user") and
      // copy_from_user(to, from, size) -> 'to' is the first argument
      node.asExpr() = call.getArgument(0) and
      // Ensure the destination is a pointer to a struct type
      node.getType().getUnspecifiedType().(PointerType).getBaseType() instanceof Struct
    )
  }

  /**
   * Sink: dereference of a pointer-typed field of the struct.
   * Identifies field accesses where a pointer field is dereferenced (e.g., p->field or (*p).field).
   */
  predicate isSink(DataFlow::Node node) {
    exists(FieldAccess fa, PointerType ptrType |
      // FieldAccess where the field is a pointer type
      fa = node.asExpr() and
      ptrType = fa.getTarget().getType().getUnspecifiedType() and
      // Ensure the field belongs to a struct
      fa.getTarget().getDeclaringType() instanceof Struct and
      // The field access is dereferenced (e.g., s->ptr_field or (*s).ptr_field)
      (
        fa instanceof PointerFieldAccess or
        fa instanceof DotFieldAccess
      ) and
      // Ensure the field access is used in a context that implies dereference
      exists(Expr parent |
        parent = fa.getParent() and
        (
          parent instanceof PointerDereferenceExpr or
          parent instanceof PointerFieldAccess or
          parent instanceof DotFieldAccess or
          parent instanceof AssignExpr or
          parent instanceof Call
        )
      )
    )
  }

  /**
   * Additional flow step: from the struct to its pointer-typed fields.
   * Tracks when a struct pointer flows to a field access of a pointer field.
   */
  predicate isAdditionalFlowStep(DataFlow::Node pred, DataFlow::Node succ) {
    exists(FieldAccess fa |
      // The successor is a field access
      succ.asExpr() = fa and
      // The field is a pointer type
      fa.getTarget().getType().getUnspecifiedType() instanceof PointerType and
      // The qualifier of the field access is the predecessor
      pred.asExpr() = fa.getQualifier() and
      // The qualifier is a pointer to a struct
      pred.getType().getUnspecifiedType().(PointerType).getBaseType() instanceof Struct
    )
  }

  /**
   * Barrier: NULL checks on the pointer field.
   * Blocks taint propagation if the pointer field is checked for NULL.
   */
  predicate isBarrier(DataFlow::Node node) {
    exists(GuardCondition guard, ComparisonOperation comp, NullValue null |
      // Guard is a comparison operation
      comp = guard.getAChild*() and
      // Comparison is == or != with NULL
      (comp.getOperator() = "==" or comp.getOperator() = "!=") and
      // One operand is the node being checked
      comp.getAnOperand() = node.asExpr() and
      // The other operand is NULL
      comp.getAnOperand() = null and
      // Ensure the guard controls the sink's basic block
      guard.controls(node.asExpr().getBasicBlock(), _)
    )
  }
}

module Flow = TaintTracking::Global<CopyFromUserStructPtrConfig>;
import Flow::PathGraph

from Flow::PathNode source, Flow::PathNode sink
where Flow::flowPath(source, sink)
select sink.getNode(), source, sink, "Dereference of pointer field copied from user space without NULL check from $@.", source.getNode(), "here"