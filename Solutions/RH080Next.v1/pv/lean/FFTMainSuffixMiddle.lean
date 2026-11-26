/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSuffixFront
import FFTMainSuffixTotal
import FFTMainSuffixQuad
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MainSuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open MainAllocation MainRootBirth RecursiveSource ApplicationBirthFrame

def isFap : InputLoader.Profile → Bool | .fap => true | .w4 => false

def middleData (p : InputLoader.Profile) (tableData outputData workData : Nat → Nat) : Role → Nat → Nat
  | .data => loadedData p | .twiddle => tableData | .output => outputData | .work => workData

def middleStatements (p : InputLoader.Profile) : List Stmt:=
  sumStatements++totalStatements (isFap p)++quadStatements p

theorem actual_w4_middle : ((bodyItems FFTRecursivePV.w4_recursive_norm_upper_ast).drop 23).take 13=middleStatements .w4 := by rfl
theorem actual_fap_middle : ((bodyItems FapFFTRecursivePV.fap_recursive_norm_upper_ast).drop 23).take 13=middleStatements .fap := by rfl

def expectedTotal (p : InputLoader.Profile) (samples : Nat → FFT.IntegerModel.CInt) : Nat:=
  NormalizeSource.totalValue (isFap p) (FFT.Limbs.ceilQuotient (OutputSumSource.partialSum samples p.grid) (1000000000^2)) p.grid

structure MiddleReady {F : Type} (state : State F) (p : InputLoader.Profile)
    (nId owner : Nat) (objects ids : Role → Nat) (pointerBase status jId : Nat)
    (tableData outputData workData : Nat → Nat) (samples : Nat → FFT.IntegerModel.CInt) : Prop where
  full : FullMainLocals state p.grid nId owner objects ids pointerBase status
  loader : Locals state InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
    (InputLoader.parameterValues ⟨p,objects .data⟩ p.count)
  arrays : ∀r,WordArrayRep state (objects r) (length p.grid r) (middleData p tableData outputData workData r)
  totalDigits : ∀k,k<6 → workData (192+k)<1000000000
  quadDigits : ∀k,k<6 → workData (208+k)<1000000000
  totalValue : FFT.Limbs.magnitude 1000000000 6 (fun k => workData (192+k))=expectedTotal p samples
  quadValue : FFT.Limbs.magnitude 1000000000 6 (fun k => workData (208+k))=QuadSource.scaledModel p
  scope : state.scope=owner
  well : WellScoped state
  distinct : Function.Injective objects

/-- Actual source instructions23..35, including genuine counter births,
accumulation, overlapping shift, upward divisions, j reset and coefficient
quadrature. All representations are propagated from the actual recursive
source output and its preserved zero accumulators. -/
theorem sum_normalize_quad {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) {before : State F}
    {nId owner pointerBase status jId : Nat} {objects ids : Role → Nat}
    {tableData outputData workData : Nat → Nat} {samples : Nat → FFT.IntegerModel.CInt}
    (full : FullMainLocals before p.grid nId owner objects ids pointerBase status)
    (loader : Locals before InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ p.count))
    (arrays : ∀r,WordArrayRep before (objects r) (length p.grid r) (middleData p tableData outputData workData r))
    (scope : before.scope=owner) (well : WellScoped before) (distinct : Function.Injective objects)
    (outputDigits : ∀k,k<p.grid → ∀d,d<5 → outputData (k*12+d)<1000000000)
    (outputValues : ∀k,k<p.grid → (ComplexSource.pair outputData (k*12)).1=(samples k).1)
    (outputSmall : ∀k,k<p.grid → (samples k).1.natAbs≤400*10^36)
    (totalZero : ∀d,d<6 → workData (192+d)=0) (quadZero : ∀d,d<6 → workData (208+d)=0) :
    ∃after finalWork,NormalSegment context before (middleStatements p) after ∧
      MiddleReady after p nId owner objects ids pointerBase status jId tableData outputData finalWork samples := by
  have programs : context.program=FFTRecursivePV.program ∨ context.program=FapFFTRecursivePV.program := by
    cases p with | fap => exact Or.inr pinned | w4 => exact Or.inl pinned
  have profilePinned : context.program=NormalizeSource.profileProgram (isFap p) := by cases p <;> exact pinned
  have nbound : 1≤p.grid ∧ p.grid≤16777216 := by cases p <;> decide
  have outNe : objects .output≠objects .work := by intro same;have bad:=distinct same;cases bad
  have dataNe : objects .data≠objects .work := by intro same;have bad:=distinct same;cases bad
  obtain ⟨sumState,sumWork,sumRun,sumFull,sumView,sumFrame,sumOutside,sumLookup,sumScope⟩ :=
    accumulate_output context programs full well scope (arrays .output) (arrays .work) outNe nbound
      outputDigits outputValues outputSmall totalZero
  have loaderSum : Locals sumState InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ p.count) := by
    apply MainTransport.locals_of_frame well loader sumFrame
    · intro v;apply sumLookup;cases v <;> decide
    · intro v;simpa using (MultiplyParameters.array_slot_different (arrays .work) (loader.slots v)).symm
  have arraySum (r : Role) (different : r≠.work) :
      WordArrayRep sumState (objects r) (length p.grid r) (middleData p tableData outputData workData r) := by
    apply MainTransport.array_of_frame well (arrays r) sumFrame
    simpa only [List.mem_singleton] using fun same => different (distinct same)
  obtain ⟨totalState,totalWork,totalRun,totalFull,totalArray,totalFrame,totalValue,totalDigits,totalOutside,totalLookup,totalScope⟩ :=
    normalize_accumulated_output context (isFap p) profilePinned sumFull sumView sumScope
  have loaderTotal : Locals totalState InputLoader.parameterName InputLoader.parameterType (loaderIds nId ids jId) owner
      (InputLoader.parameterValues ⟨p,objects .data⟩ p.count) := by
    apply MainTransport.locals_of_frame sumFrame.well loaderSum totalFrame
    · intro v;apply totalLookup;cases v <;> decide
    · intro v
      simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
      refine ⟨(MultiplyParameters.array_slot_different sumView.work (loaderSum.slots v)).symm,?_⟩
      have old:=well.objectIds _ _ (loader.slots v).object
      change loaderIds nId ids jId v≠before.nextObject
      omega
  have arrayTotal (r : Role) (different : r≠.work) :
      WordArrayRep totalState (objects r) (length p.grid r) (middleData p tableData outputData workData r) := by
    apply MainTransport.array_of_frame sumFrame.well (arraySum r different) totalFrame
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    refine ⟨fun same => different (distinct same),?_⟩
    have old:=well.objectIds _ _ (arrays r).2.1
    change objects r≠before.nextObject
    omega
  have quadZeroNow : ∀k,k<6 → totalWork (208+k)=0 := by
    intro k hk
    rw [totalOutside (208+k) (by omega),sumOutside (208+k) (by omega)]
    exact quadZero k hk
  obtain ⟨after,finalWork,quadRun,finalFull,finalLoader,finalData,finalArray,quadFrame,quadDigits,quadValue,quadOutside,finalScope⟩ :=
    construct_quad context p pinned totalFull loaderTotal (arrayTotal .data (by decide)) totalArray dataNe totalFrame.well totalScope quadZeroNow
  have arrayFinal (r : Role) (nr : r≠.work) :
      WordArrayRep after (objects r) (length p.grid r) (middleData p tableData outputData finalWork r) := by
    have rep:=arrayTotal r nr
    have sameData : middleData p tableData outputData finalWork r=middleData p tableData outputData workData r := by cases r <;> first | rfl | contradiction
    rw [sameData]
    apply MainTransport.array_of_frame totalFrame.well rep quadFrame
    simp only [List.mem_cons,List.mem_nil_iff,or_false,not_or]
    exact ⟨fun same => nr (distinct same),MultiplyParameters.array_slot_different rep (loaderTotal.slots .j)⟩
  have allFinal : ∀r,WordArrayRep after (objects r) (length p.grid r) (middleData p tableData outputData finalWork r) := by
    intro r;cases r with
    | work => exact finalArray
    | data => exact finalData
    | output => exact arrayFinal .output (by decide)
    | twiddle => exact arrayFinal .twiddle (by decide)
  have finalDigits : ∀k,k<6 → finalWork (192+k)<1000000000 := by
    intro k hk;rw [quadOutside (192+k) (by omega) (by omega)];exact totalDigits k hk
  have totalEq : FFT.Limbs.magnitude 1000000000 6 (fun k => finalWork (192+k))=
      FFT.Limbs.magnitude 1000000000 6 (fun k => totalWork (192+k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact congrArg (fun v => v*1000000000^k)
      (quadOutside (192+k) (by have h:=Finset.mem_range.mp hk;omega) (by have h:=Finset.mem_range.mp hk;omega))
  exact ⟨after,finalWork,(sumRun.append totalRun).append quadRun,
    ⟨finalFull,finalLoader,allFinal,finalDigits,quadDigits,totalEq.trans totalValue,quadValue,finalScope,quadFrame.well,distinct⟩⟩

#print axioms actual_w4_middle
#print axioms actual_fap_middle
#print axioms sum_normalize_quad
end RH080Next.FFTPV.MainSuffix
