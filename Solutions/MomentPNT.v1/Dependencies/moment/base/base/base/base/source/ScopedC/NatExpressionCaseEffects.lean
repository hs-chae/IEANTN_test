/- Expression effects under a call service preserving the separate Nat arena. -/
import ScopedC.NatLValueEffects
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

attribute [local irreducible] Machine.evalExpr Machine.evalLValue Machine.write
  Machine.read Machine.castValue Machine.addressType Machine.binaryValue
  Machine.getVar Machine.nested Machine.asNat Scalar.make Scalar.checked Scalar.binary
  List.foldlM


theorem argument_fold (cfg : Layout) (call : Call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (xs : List Expr) (acc out : List Value × State)
      (h : xs.foldlM (fun (acc,state) e => do
        let (v,last) ← evalExpr cfg call fuel state e
        pure (acc ++ [v],last)) acc = some out) : out.2.nats = acc.2.nats := by
    apply foldPair _ ?_ xs h
    intro input e result hstep
    rcases input with ⟨vs,s⟩
    cases hs : evalExpr cfg call fuel s e with
    | none => simp [hs] at hstep
    | some pair =>
        rcases pair with ⟨v,t⟩
        simp only [hs,Bind.bind,Option.bind,Pure.pure,Option.some.injEq] at hstep
        subst result
        exact he e s v t hs


/-- A pure option-valued computation returns the identical state. This proof
never unfolds the pure computation or its numerical range conditions. -/
theorem pure_result {α : Type} (input : Option α) (f : α → Value)
    {s t : State} {v : Value}
    (h : input.bind (fun a => some (f a,s)) = some (v,t)) : t.nats = s.nats := by
  cases input with
  | none => contradiction
  | some a =>
      simp only [Option.bind_some,Option.some.injEq,Prod.mk.injEq] at h
      exact (congrArg State.nats h.2).symm

theorem case_nat (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (number : Nat) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.nat number) = some (v,t) → t.nats = s.nats := by
  intro s v t h
  unfold evalExpr at h
  exact pure_result (Scalar.checked ⟨true,32⟩ (number:ℤ)) (fun a => .integer a) h

#print axioms case_nat


theorem case_uint (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (number : Nat) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.uint number) = some (v,t) → t.nats = s.nats := by
  intro s v t h
  unfold evalExpr at h
  exact pure_result (Scalar.checked ⟨false,32⟩ (number:ℤ)) (fun a => .integer a) h

#print axioms case_uint


theorem case_character (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (number : Nat) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.character number) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_character


theorem case_stringLiteral (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (text : String) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.stringLiteral text) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_stringLiteral


theorem case_conditional (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (test yes no : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.conditional test yes no) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_conditional


theorem case_var (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (name : String) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.var name) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_var


theorem case_unary (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (op : String) (arg : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.unary op arg) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  by_cases h0 : op = "&"
  all_goals by_cases h1 : op = "*"
  all_goals by_cases h2 : op = "!"
  all_goals by_cases h3 : op = "-"
  all_goals try simp only [evalExpr,h0,h1,h2,h3,Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_unary


theorem case_post (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (op : String) (arg : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.post op arg) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_post


theorem case_cast (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (type : String) (arg : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.cast type arg) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_cast


theorem case_binary (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (op : String) (left right : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.binary op left right) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  by_cases h0 : op = "="
  all_goals by_cases h1 : op = ","
  all_goals by_cases h2 : op = "&&"
  all_goals by_cases h3 : op = "||"
  all_goals try simp only [evalExpr,h0,h1,h2,h3,Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_binary


theorem case_field (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (op : String) (object : Expr) (name : String) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.field op object name) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  by_cases h0 : op = "."
  all_goals by_cases h1 : op = "->"
  all_goals try simp only [evalExpr,h0,h1,Bind.bind,Option.bind,Pure.pure] at h
  all_goals try
    have bad0 : op ≠ "." := by assumption
    have bad1 : op ≠ "->" := by assumption
    unfold evalExpr at h
    repeat' (split at h <;> (try simp_all))
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_field


theorem case_index (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (object index : Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.index object index) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  all_goals try simp only [evalExpr] at h
  all_goals try simp only [Bind.bind,Option.bind,Pure.pure] at h
  all_goals repeat' (split at h <;> (try simp_all only [Option.some.injEq,Prod.mk.injEq,Nat.add_one,Nat.succ.injEq,Expr.nat.injEq,Expr.uint.injEq,Expr.character.injEq,Expr.stringLiteral.injEq,Expr.conditional.injEq,Expr.var.injEq,Expr.unary.injEq,Expr.post.injEq,Expr.cast.injEq,Expr.binary.injEq,Expr.field.injEq,Expr.index.injEq,Expr.call.injEq,Expr.record.injEq]))
  all_goals grind only [write_nats]

#print axioms case_index


theorem case_call (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (function : Expr) (args : List Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.call function args) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  have hf := argument_fold cfg call fuel he
  cases function
  all_goals try (unfold evalExpr at h; contradiction)
  case var name =>
    unfold evalExpr at h
    let step : (List Value × State) → Expr → Option (List Value × State) := fun (acc,state) e => do
      let (value,last) ← evalExpr cfg call fuel state e
      pure (acc ++ [value],last)
    change (do
      let (values,next) ← List.foldlM step ([],s) args
      call name values next) = some (v,t) at h
    cases ha : List.foldlM step ([],s) args with
    | none => simp only [ha,Bind.bind,Option.bind] at h; contradiction
    | some pair =>
        rcases pair with ⟨vs,next⟩
        have hn : next.nats = s.nats := hf args ([],s) (vs,next) ha
        simp only [ha,Bind.bind,Option.bind] at h
        exact (keeps name vs next v t h).trans hn

#print axioms case_call


theorem case_record (cfg : Layout) (call : Call) (keeps : Preserves call) (fuel : Nat)
    (he : ∀ e s v t, evalExpr cfg call fuel s e = some (v,t) → t.nats = s.nats)
    (hl : ∀ e s a w t, evalLValue cfg call fuel s e = some (a,w,t) → t.nats = s.nats)
    (fields : List Expr) :
    ∀ s v t, evalExpr cfg call (fuel+1) s (.record fields) = some (v,t) → t.nats = s.nats := by
  change (∀ name args s v t, call name args s = some (v,t) → t.nats = s.nats) at keeps
  intro s v t h
  have hf := argument_fold cfg call fuel he
  unfold evalExpr at h
  let step : (List Value × State) → Expr → Option (List Value × State) := fun (acc,state) e => do
    let (value,last) ← evalExpr cfg call fuel state e
    pure (acc ++ [value],last)
  change (do
    let (values,next) ← List.foldlM step ([],s) fields
    pure (.aggregate values,next)) = some (v,t) at h
  cases ha : List.foldlM step ([],s) fields with
  | none => simp only [ha,Bind.bind,Option.bind] at h; contradiction
  | some pair =>
      rcases pair with ⟨vs,next⟩
      have hn : next.nats = s.nats := hf fields ([],s) (vs,next) ha
      simp only [ha,Bind.bind,Option.bind,Pure.pure,Option.some.injEq,Prod.mk.injEq] at h
      exact (congrArg State.nats h.2).symm.trans hn

#print axioms case_record

end ScopedC.NatEffects
