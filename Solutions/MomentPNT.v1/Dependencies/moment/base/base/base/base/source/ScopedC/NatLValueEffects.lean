/- Expression effects under a call service preserving the separate Nat arena. -/
import ScopedC.NatEffects
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

attribute [local irreducible] Machine.evalExpr Machine.evalLValue Machine.write
  Machine.read Machine.castValue Machine.addressType Machine.binaryValue
  Machine.getVar Machine.nested Machine.asNat Scalar.make Scalar.checked Scalar.binary
  List.foldlM

theorem lvalue_step (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats) :
    ∀ e s a w t, evalLValue cfg call (fuel+1) s e = some (a,w,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro e s a w t h
  cases e
  case unary op arg =>
    by_cases h0 : op = "*"
    all_goals try simp only [evalLValue,h0,Bind.bind,Option.bind,Pure.pure] at h
    all_goals try
      have bad : op ≠ "*" := by assumption
      unfold evalLValue at h
      repeat' (split at h <;> (try simp_all))
    all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
    all_goals grind only [write_nats]
  case field op object name =>
    by_cases h0 : op = "."
    all_goals by_cases h1 : op = "->"
    all_goals try simp only [evalLValue,h0,h1,Bind.bind,Option.bind,Pure.pure] at h
    all_goals try
      have bad0 : op ≠ "." := by assumption
      have bad1 : op ≠ "->" := by assumption
      unfold evalLValue at h
      repeat' (split at h <;> (try simp_all))
    all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
    all_goals grind only [write_nats]
  all_goals try simp only [evalLValue] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms lvalue_step
end ScopedC.NatEffects
