/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTComplexSumArguments
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ComplexSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

theorem add_step {F : Type} (context : Context F)
    (selected : findFunction context.program "fixed_add"=some fixed_add_ast)
    (compareSelected : findFunction context.program "magnitude_compare"=some magnitude_compare_ast)
    (canonSelected : findFunction context.program "canonical_sign"=some FFTRecursivePV.canonical_sign_ast)
    {before : State F} {input : Input} {ids : PVar→Nat} {owner statusId : Nat} {workData outData : Nat→Nat}
    (part : Fin 2) (h : SumView before input ids owner statusId part.val workData outData) :
    ∃after finalWork finalOut,Exec context before (StatusCall.statement "fixed_add" (addArguments part)) .normal after ∧
      SumView after input ids owner statusId (part.val+1) finalWork finalOut ∧
      MultiplyCall.CallerFrame before after [input.layout.object .output] ∧
      ∀after' flow,Exec context before (StatusCall.statement "fixed_add" (addArguments part)) flow after' →
        flow=.normal ∧ after'=after:=by
  let si:=sumInput h part
  obtain ⟨⟨after,called,post,addFrame,every⟩,statusBound,digits,bit,math⟩:=
    AddSource.fixed_add_total context selected compareSelected canonSelected before si h.well (sum_input_reps h part)
  change WordArrayRep after (input.layout.object .output) (input.layout.length (input.layout.object .output)) (AddSource.finalData si) at post
  have zeroStatus : AddSource.rawStatus si=0:=sum_input_status_zero h part
  rw [zeroStatus] at called every
  have frame : MultiplyCall.CallerFrame before after [input.layout.object .output]:=add_caller_frame addFrame
  have outsideParams : ∀r,ids r∉[input.layout.object .output]:=by
    intro r
    simpa only [List.mem_singleton,ne_eq] using
      (MultiplyParameters.array_slot_different h.output (h.params.slots r)).symm
  have outsideStatus : statusId∉[input.layout.object .output]:=by
    simpa only [List.mem_singleton,ne_eq] using
      (MultiplyParameters.array_slot_different h.output h.statusSlot).symm
  have paramsAfter:=locals_after_call h.well h.params frame outsideParams
  have slotAfter:=slot_after_call h.well h.statusSlot frame outsideStatus
  have lookupAfter : after.environment.lookup "status"=some (scalarPointer statusId .u64):=by
    rw [frame.environment]
    exact h.statusLookup
  have args:=sum_arguments_eval context h part
  have run:=StatusCall.assignment_execution h.statusLookup lookupAfter h.statusSlot slotAfter args called
  have sourceEvery:=fun s flow actual=>StatusCall.assignment_every_execution h.statusLookup lookupAfter h.statusSlot slotAfter
    (sum_arguments_closed part) args every (other:=s) (flow:=flow) actual
  let nextWork : Nat→Nat:=if input.layout.object .work=input.layout.object .output then AddSource.finalData si else workData
  have workAfter : WordArrayRep after (input.layout.object .work) (input.layout.length (input.layout.object .work)) nextWork:=by
    by_cases same : input.layout.object .work=input.layout.object .output
    · simpa only [nextWork,if_pos same,same] using post
    · have held:=word_array_after_call h.well h.work frame (by simpa only [List.mem_singleton] using same)
      simpa only [nextWork,if_neg same] using held
  have pb:=part.isLt
  have workBound : input.layout.start .work+46≤ input.layout.length (input.layout.object .work):=by simpa using input.layout.bound MultiplyParameters.Var.work
  have workPreserved : ∀j : Fin 4,∀k,k<6 →
      nextWork (input.layout.start .work+6*j.val+k)=workData (input.layout.start .work+6*j.val+k):=by
    intro j k hk
    by_cases same : input.layout.object .work=input.layout.object .output
    · have outside : input.layout.start .work+6*j.val+k< input.layout.start .output+6*part.val ∨
          input.layout.start .output+6*part.val+6≤ input.layout.start .work+6*j.val+k:=by
        have jb:=j.isLt
        rcases input.disjoint MultiplyParameters.Var.output (by decide) with no|low|high
        · exact False.elim (no same.symm)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have kept:=AddSource.finalData_outside si (input.layout.start .work+6*j.val+k) outside
      change AddSource.finalData si (input.layout.start .work+6*j.val+k)=sumData input workData outData (input.layout.object .output) (input.layout.start .work+6*j.val+k) at kept
      have old:=sum_data_work_value h (index:=input.layout.start .work+6*j.val+k) (by have jb:=j.isLt;omega)
      simpa only [nextWork,if_pos same] using kept.trans (by simpa only [same] using old)
    · simp only [nextWork,if_neg same]
  have productsAfter : ∀j : Fin 4,ProductAt input nextWork j:=by
    intro j
    have old:=h.products j
    refine ⟨(represented_congr nextWork workData _ _ (workPreserved j)).trans old.1,?_,?_⟩
    · intro k hk
      rw [workPreserved j k (by omega)]
      exact old.2.1 k hk
    · rw [workPreserved j 5 (by omega)]
      exact old.2.2
  have newComponent : ComponentAt input (AddSource.finalData si) part:=by
    have calculated:=math zeroStatus
    have leftRep : CanonicalSource.represented (sumData input workData outData (input.layout.object .work))
        (input.layout.start .work+6*(leftProduct part).val)=
      CanonicalSource.represented workData (input.layout.start .work+6*(leftProduct part).val):=by
      apply represented_congr
      intro k hk
      exact sum_data_work_value h (by have jb:=(leftProduct part).isLt;omega)
    have rightRep : CanonicalSource.represented (sumData input workData outData (input.layout.object .work))
        (input.layout.start .work+6*(rightProduct part).val)=
      CanonicalSource.represented workData (input.layout.start .work+6*(rightProduct part).val):=by
      apply represented_congr
      intro k hk
      exact sum_data_work_value h (by have jb:=(rightProduct part).isLt;omega)
    change CanonicalSource.represented (AddSource.finalData si) (input.layout.start .output+6*part.val)=
      (if 0<(if part.val=0 then 1 else 0) then
        CanonicalSource.represented (sumData input workData outData (input.layout.object .work)) (input.layout.start .work+6*(leftProduct part).val)-
          CanonicalSource.represented (sumData input workData outData (input.layout.object .work)) (input.layout.start .work+6*(rightProduct part).val)
       else CanonicalSource.represented (sumData input workData outData (input.layout.object .work)) (input.layout.start .work+6*(leftProduct part).val)+
          CanonicalSource.represented (sumData input workData outData (input.layout.object .work)) (input.layout.start .work+6*(rightProduct part).val)) at calculated
    rw [leftRep,rightRep,(h.products (leftProduct part)).1,(h.products (rightProduct part)).1] at calculated
    refine ⟨?_,digits,bit⟩
    fin_cases part <;> simpa [leftProduct,rightProduct,sumValue] using calculated
  have componentsAfter : ∀c : Fin 2,c.val< part.val+1 →ComponentAt input (AddSource.finalData si) c:=by
    intro c hc
    by_cases same : c=part
    · simpa only [same] using newComponent
    · have past : c.val< part.val:=by have ne:=fun eq=>same (Fin.ext eq);omega
      have old:=h.components c past
      have preserved : ∀k,k<6 →AddSource.finalData si (input.layout.start .output+6*c.val+k)=outData (input.layout.start .output+6*c.val+k):=by
        intro k hk
        have kept:=AddSource.finalData_outside si (input.layout.start .output+6*c.val+k) (Or.inl (by
          change input.layout.start .output+6*c.val+k< input.layout.start .output+6*part.val
          omega))
        simpa [si,sumInput,sumLayout,sumObject,sumData] using kept
      refine ⟨(represented_congr _ _ _ _ preserved).trans old.1,?_,?_⟩
      · intro k hk
        rw [preserved k (by omega)]
        exact old.2.1 k hk
      · rw [preserved 5 (by omega)]
        exact old.2.2
  have outsideWorkAfter : ∀k,k< input.layout.length (input.layout.object .work) →
      (k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
      (input.layout.object .work≠input.layout.object .output ∨ k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
      nextWork k=input.old (input.layout.object .work) k:=by
    intro k bound outsideWork outsideOut
    by_cases same : input.layout.object .work=input.layout.object .output
    · have outside : k<si.layout.start .out ∨ si.layout.start .out+6≤k:=by
        change k< input.layout.start .output+6*part.val ∨ input.layout.start .output+6*part.val+6≤k
        rcases outsideOut with no|low|high
        · exact False.elim (no same)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      have kept:=AddSource.finalData_outside si k outside
      change AddSource.finalData si k=sumData input workData outData (input.layout.object .output) k at kept
      have old:=sum_data_work_value h (index:=k) bound
      have sameValue : AddSource.finalData si k=workData k:=kept.trans (by simpa only [same] using old)
      simpa only [nextWork,if_pos same] using sameValue.trans (h.outsideWork k bound outsideWork outsideOut)
    · simpa only [nextWork,if_neg same] using h.outsideWork k bound outsideWork outsideOut
  have outsideOutputAfter : ∀k,k< input.layout.length (input.layout.object .output) →
      (k< input.layout.start .output ∨ input.layout.start .output+12≤k) →
      (input.layout.object .output≠input.layout.object .work ∨ k< input.layout.start .work ∨ input.layout.start .work+46≤k) →
      AddSource.finalData si k=input.old (input.layout.object .output) k:=by
    intro k bound outsideOut outsideWork
    have kept:=AddSource.finalData_outside si k (by
      change k< input.layout.start .output+6*part.val ∨ input.layout.start .output+6*part.val+6≤k
      omega)
    have kept' : AddSource.finalData si k=outData k:=by
      simpa [si,sumInput,sumLayout,sumObject,sumData] using kept
    exact kept'.trans (h.outsideOutput k bound outsideOut outsideWork)
  exact ⟨after,nextWork,AddSource.finalData si,run,
    ⟨paramsAfter,lookupAfter,slotAfter,workAfter,post,productsAfter,componentsAfter,
      outsideWorkAfter,outsideOutputAfter,by omega,frame.frame.well⟩,frame,sourceEvery⟩

#print axioms add_step
end RH080Next.FFTPV.ComplexSource
