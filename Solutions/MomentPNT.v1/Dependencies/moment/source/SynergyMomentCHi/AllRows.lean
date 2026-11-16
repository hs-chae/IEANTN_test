/- All concrete point/suffix providers and the normal checked I/O model are
instantiated. No numerical/application-success premise remains. -/
import SynergyMomentCHi.WorldLoop
import SourceMomentFamilyV1.All
import SourceMainFramesV1.AllExecution
import SourceHeightEdgesV1.All
import SynergyMomentC.WordValues
import SynergyHeightC.MainIOTrace
namespace SynergyMomentCHi.AllRows
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
open SynergyHeightC.MainWeightModel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

theorem budget_from_model (kind : Kind) (i : Nat) (hi : i < 768) (c d : ProofBox)
 (model : PointExecuteAPI.modelOutputs (MainInputPointComposition.input i)=some (c,d)) :
 Budget.run kind (FamilyAPI.total kind i) i c d=some
  (.continuing (BudgetProposed.afterProposed (FamilyAPI.total kind i)
    (FamilyAPI.total kind (i+1)) i c d)) := by
 obtain ⟨_,_,canonical,_⟩:=domain_spec (i:=i) (SourceMainWeightsV1.All.all_domains i hi)
 have input:=congrFun MainIOTrace.source_input_function_exact i
 have actual : PointExecuteAPI.modelOutputs (gridInput (i+1))=some (c,d) :=
  (congrArg PointExecuteAPI.modelOutputs input).symm.trans model
 have pair : (c,d)=modelPair i:=Option.some.inj (actual.symm.trans canonical)
 have words : Model.highPair (c,d)=SourceMomentWordsV1.All.word i :=
  (congrArg Model.highPair pair).trans (@WordValues.source_words i hi)
 have ch:=congrArg Prod.fst words
 have dh:=congrArg Prod.snd words
 change c.hi+(ProofBox.literal 128 21600 1).hi=(SourceMomentWordsV1.All.word i).1 at ch
 rw [literal_shift] at ch
 have chi : c.hi=(SourceMomentWordsV1.All.word i).1-21600*ProofBox.scale 128 := by omega
 change d.hi=(SourceMomentWordsV1.All.word i).2 at dh
 have cSame : c=FamilyAPI.c i c.lo := by
  cases c with
  | mk low high=>
   change (⟨low,high⟩ : ProofBox)=⟨low,(SourceMomentWordsV1.All.word i).1-21600*ProofBox.scale 128⟩
   exact congrArg (fun h : Int=>(⟨low,h⟩ : ProofBox)) chi
 have dSame : d=FamilyAPI.d i d.lo := by
  cases d with
  | mk low high=>
   change (⟨low,high⟩ : ProofBox)=⟨low,(SourceMomentWordsV1.All.word i).2⟩
   exact congrArg (fun h : Int=>(⟨low,h⟩ : ProofBox)) dh
 have execution:=SourceMomentFamilyV1.All.rows kind i hi c.lo d.lo
 rw [←cSame,←dSame] at execution
 exact execution

theorem stdout_unshadowed (total next : ProofBox) (i : Nat) (c d : ProofBox) :
 (BudgetProposed.afterProposed total next i c d).globals.lookup "stdout"=none := by rfl

theorem actual_row (kind : Kind) (platform : WorldIO.Platform) (initial : Stream)
 (i : Nat) (hi : i < 768) :
 WorldLoop.RowRun kind platform CompleteIOModel.policy (FamilyAPI.total kind)
  (MainIOTrace.streams initial) i := by
 obtain ⟨input,pair,defined,model,pointRun⟩:=SourceMainFramesV1.AllExecution.executions
  i hi (FamilyAPI.total kind i)
 have sameInput : MainInputPointComposition.input i=input := by
  simp only [MainInputPointComposition.input,defined,Option.getD_some]
 rw [←sameInput] at model pointRun
 have budget:=budget_from_model kind i hi pair.1 pair.2 model
 have words:=MainIOTrace.words_of_outputs (i:=i) (c:=pair.1) (d:=pair.2) hi model
 have ranges:=MainIOTrace.word_ranges i hi
 have cRange : SynergyC.Word512.Range (adjustedC pair.1).hi := by
  rw [words.1];exact ranges.1
 have dRange : SynergyC.Word512.Range pair.2.hi := by
  rw [words.2];exact ranges.2
 let state:=BudgetProposed.afterProposed (FamilyAPI.total kind i) (FamilyAPI.total kind (i+1))
  i pair.1 pair.2
 let middle : WorldIO.World:=⟨state,CompleteIOModel.appendWord
   (MainIOTrace.streams initial i) (adjustedC pair.1).hi⟩
 let after : WorldIO.World:=⟨state,CompleteIOModel.appendWord
   (CompleteIOModel.appendWord (MainIOTrace.streams initial i) (adjustedC pair.1).hi) pair.2.hi⟩
 have first : EmitUService.call platform CompleteIOModel.policy "emitU"
   [SynergyC.Word512.value (adjustedC pair.1).hi]
   ⟨state,MainIOTrace.streams initial i⟩=some (.unit,middle) :=
  CompleteIOModel.emitU_success platform state (adjustedC pair.1).hi cRange
    (MainIOTrace.streams initial i) (stdout_unshadowed _ _ _ _ _)
 have second : EmitUService.call platform CompleteIOModel.policy "emitU"
   [SynergyC.Word512.value pair.2.hi] middle=some (.unit,after) :=
  CompleteIOModel.emitU_success platform state pair.2.hi dRange
    (CompleteIOModel.appendWord (MainIOTrace.streams initial i) (adjustedC pair.1).hi)
    (stdout_unshadowed _ _ _ _ _)
 have body:=(WorldIteration.actual_body kind platform CompleteIOModel.policy
   (SourceHeightEdgesV1.All.edges i hi) (FamilyAPI.total kind i) (FamilyAPI.total kind (i+1))
   pair.1 pair.2 (by omega) pointRun budget (MainIOTrace.streams initial i) middle after
   first second).1
 have stream : after.stream=MainIOTrace.streams initial (i+1) := by
  change CompleteIOModel.appendWord
   (CompleteIOModel.appendWord (MainIOTrace.streams initial i) (adjustedC pair.1).hi) pair.2.hi=
   CompleteIOModel.appendWord
    (CompleteIOModel.appendWord (MainIOTrace.streams initial i) (MainIOTrace.cWord i))
    (MainIOTrace.dWord i)
  rw [words.1,words.2]
 rw [stream] at body
 exact body
#print axioms budget_from_model
#print axioms stdout_unshadowed
#print axioms actual_row
end
end SynergyMomentCHi.AllRows
