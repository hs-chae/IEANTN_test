/- Ordinary automatic storage and parameter binding preserve the Nat arena. -/
import ScopedC.NatExpressionEffects
namespace ScopedC.NatEffects
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
attribute [local irreducible] Machine.evalExpr Machine.evalLValue Machine.write
  Machine.read Machine.castValue Machine.addressType Machine.binaryValue
  Machine.getVar Machine.nested Machine.asNat Scalar.make Scalar.checked Scalar.binary
  List.foldlM Machine.declarations ArrayDeclarations.elements

theorem legacy_declarations {cfg : Layout} {call : Call} (keeps : Preserves call)
    {ds : List Decl} {s t : State} (h : Machine.declarations cfg call ds s = some t) :
    t.nats = s.nats := by
  unfold Machine.declarations at h
  apply foldState _ ?_ ds h
  intro current d after step
  have he : ∀ (e : Expr) (s : State) (v : Value) (t : State),
      evalExpr cfg call 1000 s e = some (v,t) → t.nats = s.nats :=
    fun _ _ _ _ h => expression keeps h
  simp only [Bind.bind,Option.bind,Pure.pure] at step
  repeat' (split at step <;> (try simp_all))
  all_goals grind only [allocate_nats]

theorem array_elements {cfg : Layout} {call : Call} (keeps : Preserves call)
    {object index : Nat} {es : List Expr} {s t : State}
    (h : ArrayDeclarations.elements cfg call object index es s = some t) :
    t.nats = s.nats := by
  induction es generalizing index s with
  | nil =>
      have hs : s = t := Option.some.inj (by simpa only [ArrayDeclarations.elements] using h)
      exact (congrArg State.nats hs).symm
  | cons e es ih =>
      cases he : evalExpr cfg call 1000 s e with
      | none => simp [ArrayDeclarations.elements,he] at h
      | some pair =>
          rcases pair with ⟨v,u⟩
          cases hw : write cfg u ⟨object,index,[]⟩ true v with
          | none => simp [ArrayDeclarations.elements,he,hw] at h
          | some result =>
              rcases result with ⟨stored,next⟩
              have ht : ArrayDeclarations.elements cfg call object (index+1) es next = some t := by
                simpa only [ArrayDeclarations.elements,he,hw,Bind.bind,Option.bind] using h
              exact (ih ht).trans ((write_nats hw).trans (expression keeps he))

theorem array_one {cfg : Layout} {call : Call} (keeps : Preserves call)
    {d : Decl} {s t : State} (h : ArrayDeclarations.one cfg call d s = some t) :
    t.nats = s.nats := by
  cases ha : d.arrayExtent with
  | none =>
      rw [ArrayDeclarations.one_legacy (Or.inl (by simp [ha]))] at h
      exact legacy_declarations keeps h
  | some extent =>
      cases hv : d.value with
      | none =>
          rw [ArrayDeclarations.one_legacy (Or.inr (by simp [hv]))] at h
          exact legacy_declarations keeps h
      | some e =>
          cases e <;> (try simp only [ArrayDeclarations.one,ha,hv,Bind.bind,Option.bind] at h)
          all_goals repeat' (split at h <;> (try simp_all))
          all_goals try contradiction
          all_goals exact (array_elements keeps h.2).trans (allocateArray_nats _ _ _ _)

theorem array_declarations {cfg : Layout} {call : Call} (keeps : Preserves call)
    {ds : List Decl} {s t : State}
    (h : ArrayDeclarations.declarations cfg call ds s = some t) : t.nats = s.nats := by
  exact foldState _ (fun _ _ _ h => array_one keeps h) ds h

theorem bind_arguments {cfg : Layout} {parameters : List (String × String)}
    {args : List Value} {s t : State} (h : bindArgs cfg parameters args s = some t) :
    t.nats = s.nats := by
  unfold bindArgs at h
  split at h
  · contradiction
  · apply foldState _ ?_ (parameters.zip args) h
    intro current item after step
    simp only [Bind.bind,Option.bind,Pure.pure] at step
    repeat' (split at step <;> (try simp_all))
    all_goals exact (congrArg State.nats step).symm

#print axioms legacy_declarations
#print axioms array_elements
#print axioms array_one
#print axioms array_declarations
#print axioms bind_arguments
end ScopedC.NatEffects
