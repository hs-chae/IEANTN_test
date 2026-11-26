/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTAddStart
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.AddSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings
open FFT.Limbs
open IncrementSource (base)

def signedData (input : Input) (sub swap : Bool) (sign : Nat) : Nat → Nat:=
  Function.update (currentData input.old (input.layout.object .out) (input.layout.start .out)
    sub (input.left swap) (input.right swap) 5 (input.layout.object .out)) (input.layout.start .out+5) sign

structure BranchView {F : Type} (state : State F) (input : Input) (sub swap : Bool) (sign status owner : Nat)
    (li : Var → Nat) : Prop where
  array : WordArrayRep state (input.layout.object .out) (input.layout.length (input.layout.object .out)) (signedData input sub swap sign)
  locals : Locals state name type li owner (values input 5 status)
  separate : ∀v,input.layout.object .out≠li v
  well : WellScoped state

theorem store_sign_execution {F : Type} (context : Context F) {before : State F} {input : Input} {sub swap : Bool}
    {owner cutoff sign : Nat} {li : Var → Nat} (h : View before input sub swap owner li 5)
    (rhs : Expr) (read : Eval context before rhs (.integer (integer64 sign)) before)
    (sign64 : sign < 2^64) (fresh : cutoff ≤ before.nextObject) :
    ∃after,Exec context before (.assign (.index (.variable "out") (.literal (.integer 5 "ULL"))) rhs) .normal after ∧
      BranchView after input sub swap sign (scan sub (input.left swap) (input.right swap) 5).2 owner li ∧
      ApplicationBirthFrame.Frame cutoff before after (writes input li) := by
  have hi : input.layout.start .out+5 < input.layout.length (input.layout.object .out):=by have hb:=input.layout.bound .out; omega
  obtain ⟨after,stored,rep⟩:=word_store_with_rep (h.arrays .out) hi sign64
  have run : Exec context before (.assign (.index (.variable "out") (.literal (.integer 5 "ULL"))) rhs) .normal after:=
    .assign read (.index (.variable (h.locals.lookup Var.out) (h.locals.read Var.out))
      (.literal (.integer 5 "ULL") _ (.integer (integer64 5)) (by rfl)) (slice_pointer_add (h.arrays .out) hi)) stored
  have locals:=ApplicationBirthFrame.locals_store_other h.locals (fun v=>(h.separate .out v).symm) stored
  have frame:=ApplicationBirthFrame.store_frame cutoff (writes input li) h.well fresh (Or.inl (by simp [writes,wordPointer])) stored
  exact ⟨after,run,⟨rep,locals,h.separate .out,frame.well⟩,frame⟩

theorem add_branch_execution {F : Type} (context : Context F) {before : State F} {input : Input}
    {owner : Nat} {li : Var → Nat} (h : View before input false false owner li 0) :
    ∃after,Exec context before additionBranch .normal after ∧
      BranchView after input false false input.asign (scan false (input.left false) (input.right false) 5).2 owner li ∧
      ApplicationBirthFrame.Frame before.nextObject before after (writes input li) := by
  obtain ⟨middle,loopRun,post,loopFrame⟩:=add_loop_execution context 5 (j:=0) (by omega) h.enter
  have sign64 : input.asign < 2^64:=lt_of_le_of_lt input.signA (by norm_num)
  obtain ⟨last,signRun,branch,signFrame⟩:=store_sign_execution context post (.variable "as")
    (.variable (post.locals.lookup Var.asign) (post.locals.read Var.asign)) sign64 loopFrame.fresh
  have full:=ApplicationBirthFrame.close_frame h.well (le_refl _) (loopFrame.trans signFrame)
  let after : State F:={last.leaveScope before.nextScope before.environment with scope:=before.scope}
  have different : before.nextScope≠owner:=by have ho:=h.locals.bound; omega
  have locals:=branch.locals.leave different before.environment h.locals.lookup before.scope
  exact ⟨after,.block (by rfl) (.cons loopRun (.cons signRun .nil)) (by rfl),
    ⟨IncrementSource.wordArray_leave branch.array,locals,h.separate .out,full.well⟩,full⟩

#print axioms store_sign_execution
#print axioms add_branch_execution
end RH080Next.FFTPV.AddSource
