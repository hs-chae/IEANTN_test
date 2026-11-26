/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddData
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

inductive Array where | out | a | b deriving DecidableEq

structure Layout where
  object : Array → Nat
  start : Array → Nat
  length : Nat → Nat
  bound : ∀r,start r+6 ≤ length (object r)
  safeA : SafeAlias (object .out) (start .out) (object .a) (start .a)
  safeB : SafeAlias (object .out) (start .out) (object .b) (start .b)

def Arrays {F : Type} (state : State F) (layout : Layout) (old : Nat → Nat → Nat)
    (sub : Bool) (a b : Nat → Nat) (j : Nat) : Prop :=
  ∀r,WordArrayRep state (layout.object r) (layout.length (layout.object r))
    (currentData old (layout.object .out) (layout.start .out) sub a b j (layout.object r))

/-- All overlapping views refer to one actual object and one data function.
This prevents falsely claiming that an aliased original input is unchanged. -/
theorem Arrays.store_digit {F : Type} {state : State F} {layout : Layout} {old : Nat → Nat → Nat}
    {sub : Bool} {a b : Nat → Nat} {j : Nat} (h : Arrays state layout old sub a b j) (hj : j < 5) :
    ∃after,state.store (wordPointer (layout.object .out) (layout.start .out+j))
        (.integer (integer64 ((digitTotal sub (a j) (b j) (scan sub a b j).2)%base)))=some after ∧
      Arrays after layout old sub a b (j+1) := by
  have hi : layout.start .out+j < layout.length (layout.object .out) := by
    have hb:=layout.bound .out
    omega
  have hv : (digitTotal sub (a j) (b j) (scan sub a b j).2)%base < 2^64 :=
    lt_trans (Nat.mod_lt _ (by norm_num [base])) (by norm_num [base])
  obtain ⟨after,stored,rep⟩:=word_store_with_rep (h .out) hi hv
  rw [currentData_step] at rep
  refine ⟨after,stored,?_⟩
  intro r
  by_cases same : layout.object r=layout.object .out
  · simpa only [same] using rep
  · have oldRep:=h r
    have preserved:=IncrementSource.array_store_other oldRep
      (show layout.object r≠(wordPointer (layout.object .out) (layout.start .out+j)).object from same) stored
    have unchanged (k : Nat) : currentData old (layout.object .out) (layout.start .out) sub a b k (layout.object r)=old (layout.object r) := by
      funext i
      simp [currentData,same]
    rw [unchanged j] at preserved
    rw [unchanged (j+1)]
    exact preserved

theorem Arrays.enter {F : Type} {state : State F} {layout : Layout} {old : Nat → Nat → Nat}
    {sub : Bool} {a b : Nat → Nat} {j : Nat} (h : Arrays state layout old sub a b j) :
    Arrays state.enterScope layout old sub a b j:=h

theorem Arrays.declare_old {F : Type} {before after : State F} {layout : Layout} {old : Nat → Nat → Nat}
    {sub : Bool} {a b : Nat → Nat} {j : Nat} {cname : String} {ctype : CType} {value : Value}
    (well : WellScoped before) (h : Arrays before layout old sub a b j)
    (declared : Declaration before after cname ctype value) : Arrays after layout old sub a b j :=
  fun r=>ApplicationBirthFrame.array_declare_old well (h r) declared

theorem Arrays.store_other {F : Type} {before after : State F} {layout : Layout} {old : Nat → Nat → Nat}
    {sub : Bool} {a b : Nat → Nat} {j : Nat} {pointer : Pointer} {value : Value}
    (h : Arrays before layout old sub a b j) (different : ∀r,layout.object r≠pointer.object)
    (stored : before.store pointer value=some after) : Arrays after layout old sub a b j :=
  fun r=>IncrementSource.array_store_other (h r) (different r) stored

theorem Arrays.leave {F : Type} {state : State F} {layout : Layout} {old : Nat → Nat → Nat}
    {sub : Bool} {a b : Nat → Nat} {j scope restore : Nat} {environment : List (String×Pointer)}
    (h : Arrays state layout old sub a b j) :
    Arrays {state.leaveScope scope environment with scope:=restore} layout old sub a b j:=
  fun r=>IncrementSource.wordArray_leave (h r)

theorem source_index_eval {F : Type} (context : Context F) {state : State F} {layout : Layout}
    {old : Nat → Nat → Nat} {sub : Bool} {a b : Nat → Nat} {j : Nat}
    (h : Arrays state layout old sub a b j) (role : Array) (safe : role≠.out)
    (arrayExpr indexExpr : Expr)
    (arrayRead : Eval context state arrayExpr (.pointer (wordPointer (layout.object role) (layout.start role))) state)
    (indexRead : Eval context state indexExpr (.integer (integer64 j)) state) (hj : j < 5) :
    Eval context state (.index arrayExpr indexExpr)
      (.integer (integer64 (old (layout.object role) (layout.start role+j)))) state := by
  have hi : layout.start role+j < layout.length (layout.object role) := by have hb:=layout.bound role; omega
  have run : Eval context state (.index arrayExpr indexExpr)
      (.integer (integer64 (currentData old (layout.object .out) (layout.start .out) sub a b j
        (layout.object role) (layout.start role+j)))) state:=
    .load (.index arrayRead indexRead (slice_pointer_add (h role) hi)) (word_load (h role) hi)
  have aliasSafe : SafeAlias (layout.object .out) (layout.start .out) (layout.object role) (layout.start role) := by
    cases role with
    | out=>exact False.elim (safe rfl)
    | a=>exact layout.safeA
    | b=>exact layout.safeB
  simpa only [currentData_unread old _ _ _ _ aliasSafe sub a b j hj] using run

#print axioms Arrays.store_digit
#print axioms source_index_eval
end RH080Next.FFTPV.AddSource
