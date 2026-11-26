/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexComponents
import FFTFixedMultiplyCorrectWords
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem multiply_step {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_multiply"=some fixed_multiply_ast)
    (zeroSelected : findFunction context.program "zero_words"=some zero_words_ast)
    (incSelected : findFunction context.program "increment_words"=some increment_words_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {ids : PVar→Nat} {owner statusId : Nat} {workData : Nat→Nat}
    (i : Fin 4) (h : View before input ids owner statusId i.val workData) :
    ∃after finalWork,Exec context before (StatusCall.statement "fixed_multiply" (multiplyArguments i)) .normal after ∧
      View after input ids owner statusId (i.val+1) finalWork ∧
      MultiplyCall.CallerFrame before after [input.layout.object .work] ∧
      ∀after' flow,Exec context before (StatusCall.statement "fixed_multiply" (multiplyArguments i)) flow after' →
        flow=.normal ∧ after'=after:=by
  let l:=input.layout
  let d:=dataAt input workData
  have workRep : WordArrayRep before (l.object .work) (l.length (l.object .work)) workData:=by
    simpa [d,l,dataAt] using h.arrays MultiplyParameters.Var.work
  obtain ⟨ad,ab,am,ar⟩:=component_properties h .a (Or.inl rfl) (aOffset i) (aOffset_cases i)
  obtain ⟨bd,bb,bm,br⟩:=component_properties h .b (Or.inr rfl) (bOffset i) (bOffset_cases i)
  have ao : aOffset i≤6:=by rcases aOffset_cases i with eq|eq <;> omega
  have bo : bOffset i≤6:=by rcases bOffset_cases i with eq|eq <;> omega
  have iw:=i.isLt
  have workBound : l.start .work+46≤l.length (l.object .work):=by simpa [l] using l.bound MultiplyParameters.Var.work
  have aBound : l.start .a+12≤l.length (l.object .a):=by simpa [l] using l.bound MultiplyParameters.Var.a
  have bBound : l.start .b+12≤l.length (l.object .b):=by simpa [l] using l.bound MultiplyParameters.Var.b
  have aDisjoint : l.object .a≠l.object .work ∨ l.start .a+aOffset i+6≤l.start .work+36 ∨
      l.start .work+36+10≤l.start .a+aOffset i:=by
    rcases input.disjoint .a (by decide) with no|low|high
    · exact Or.inl no
    · exact Or.inr (Or.inl (by dsimp [l];omega))
    · exact Or.inr (Or.inr (by dsimp [l];omega))
  have bDisjoint : l.object .b≠l.object .work ∨ l.start .b+bOffset i+6≤l.start .work+36 ∨
      l.start .work+36+10≤l.start .b+bOffset i:=by
    rcases input.disjoint .b (by decide) with no|low|high
    · exact Or.inl no
    · exact Or.inr (Or.inl (by dsimp [l];omega))
    · exact Or.inr (Or.inr (by dsimp [l];omega))
  obtain ⟨after,finalWork,called,post,math,digits,bit,workWords,outWords,frame,every⟩:=
    MultiplyCall.fixed_multiply_correct_words context selected zeroSelected incSelected canonSelected before
      (l.object .work) (l.length (l.object .work)) (l.start .work+6*i.val)
      (l.object .a) (l.length (l.object .a)) (l.start .a+aOffset i)
      (l.object .b) (l.length (l.object .b)) (l.start .b+bOffset i)
      (l.object .work) (l.length (l.object .work)) (l.start .work+36)
      workData (d (l.object .a)) (d (l.object .b)) workData h.well workRep workRep (h.arrays .a) (h.arrays .b)
      (fun eq=>congrArg l.length eq) (fun eq=>congrArg l.length eq) (fun _=>rfl)
      aDisjoint bDisjoint (Or.inr (Or.inl (by omega))) (by omega) (by omega) (by omega) (by omega)
      ad bd ab bb am bm
  have workFrame : MultiplyCall.CallerFrame before after [l.object .work]:=by
    refine ⟨frame.environment,frame.scope,frame.frame.well,frame.frame.fresh,frame.frame.nextObject,
      frame.frame.nextScope,frame.frame.mode,frame.frame.foreign,?_⟩
    intro id old outside
    exact frame.frame.outside id old (by simpa using outside)
  have outsideParams : ∀r,ids r∉[l.object .work]:=by
    intro r
    simpa only [List.mem_singleton,ne_eq] using
      (MultiplyParameters.array_slot_different workRep (h.params.slots r)).symm
  have outsideStatus : statusId∉[l.object .work]:=by
    simpa only [List.mem_singleton,ne_eq] using
      (MultiplyParameters.array_slot_different workRep h.statusSlot).symm
  have paramsAfter:=locals_after_call h.well h.params workFrame outsideParams
  have slotAfter:=slot_after_call h.well h.statusSlot workFrame outsideStatus
  have lookupAfter : after.environment.lookup "status"=some (scalarPointer statusId .u64):=by
    rw [workFrame.environment]
    exact h.statusLookup
  have args:=multiply_arguments_eval context h.params h.arrays i
  have called' : Call context "fixed_multiply" (multiplyValues input.layout i) before
      (.value (.integer (integer64 0))) after:=called
  have run:=StatusCall.assignment_execution h.statusLookup lookupAfter h.statusSlot slotAfter args called'
  have callback : ∀s result,Call context "fixed_multiply" (multiplyValues input.layout i) before result s →
      result=.value (.integer (integer64 0)) ∧ s=after:=every
  have sourceEvery:=fun s flow actual=>StatusCall.assignment_every_execution h.statusLookup lookupAfter h.statusSlot slotAfter
    (multiply_arguments_closed i) args callback (other:=s) (flow:=flow) actual
  have arraysAfter : ∀r,WordArrayRep after (l.object r) (l.length (l.object r)) (dataAt input finalWork (l.object r)):=by
    intro r
    by_cases same : l.object r=l.object .work
    · have same' : input.layout.object r=input.layout.object .work:=same
      simpa [l,dataAt,same'] using post
    · have same' : input.layout.object r≠input.layout.object .work:=same
      have held:=word_array_after_call h.well (h.arrays r) workFrame (by simpa only [List.mem_singleton,l] using same')
      simpa [l,dataAt,same'] using held
  have inputAfter : ∀r,r=MultiplyParameters.Var.a ∨ r=MultiplyParameters.Var.b →∀k,k<12 →
      dataAt input finalWork (l.object r) (l.start r+k)=input.old (l.object r) (l.start r+k):=by
    intro r role k hk
    by_cases same : l.object r=l.object .work
    · have notWork : r≠MultiplyParameters.Var.work:=by rcases role with rfl|rfl <;> decide
      have disjoint:=input.disjoint r notWork
      have bound:=l.bound r
      have extent : l.start r+12≤l.length (l.object r):=by simpa [notWork] using bound
      have outsideWindow : l.start r+k<l.start .work ∨ l.start .work+46≤l.start r+k:=by
        rcases disjoint with no|low|high
        · exact False.elim (no same)
        · exact Or.inl (by dsimp [l] at *;omega)
        · exact Or.inr (by dsimp [l] at *;omega)
      have kept:=outWords (l.start r+k) (by rw [same] at extent;omega)
        (by omega) (Or.inr (by omega))
      have previous:=h.inputValues r role k hk
      have same' : input.layout.object r=input.layout.object .work:=same
      simpa [dataAt,l,same'] using kept.trans (by simpa [dataAt,l,same'] using previous)
    · have same' : input.layout.object r≠input.layout.object .work:=same
      simp [dataAt,l,same']
  have productsAfter : ∀j : Fin 4,j.val< i.val+1 → ProductAt input finalWork j:=by
    intro j hj
    by_cases same : j=i
    · subst j
      refine ⟨?_,digits,bit⟩
      rw [ar,br] at math
      have scale : (1000000000^4:Nat)=unit:=by norm_num [unit]
      simpa only [scale,productValue,l] using math
    · have past : j.val< i.val:=by have ne:=fun eq=>same (Fin.ext eq);omega
      have old:=h.products j past
      have preserved : ∀k,k<6 → finalWork (l.start .work+6*j.val+k)=workData (l.start .work+6*j.val+k):=by
        intro k hk
        exact outWords _ (by omega) (by omega) (Or.inr (Or.inl (by omega)))
      have valueSame:=represented_congr finalWork workData (l.start .work+6*j.val) (l.start .work+6*j.val) preserved
      refine ⟨valueSame.trans old.1,?_,?_⟩
      · intro k hk
        rw [preserved k (by omega)]
        exact old.2.1 k hk
      · rw [preserved 5 (by omega)]
        exact old.2.2
  have outsideWork : ∀k,k< input.layout.length (input.layout.object .work) →
      (k< input.layout.start .work ∨ input.layout.start .work+46≤k) → finalWork k=input.old (input.layout.object .work) k:=by
    intro k bound outside
    have unchanged:=outWords k bound (by dsimp [l];omega) (Or.inr (by dsimp [l];omega))
    exact unchanged.trans (h.outsideWork k bound outside)
  exact ⟨after,finalWork,run,⟨paramsAfter,lookupAfter,slotAfter,arraysAfter,inputAfter,productsAfter,outsideWork,by omega,workFrame.frame.well⟩,
    workFrame,sourceEvery⟩

#print axioms multiply_step
end RH080Next.FFTPV.ComplexSource
