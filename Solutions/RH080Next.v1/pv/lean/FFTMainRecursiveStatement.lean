import FFTMainRecursiveStatementBase
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainRecursiveStatement
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource MainRootBirth
open MainCertificate MainAllocation

def roleData (p : InputLoader.Profile) (tableData outputData workData : Nat→Nat) : Role→Nat→Nat
  | .data=>MainSuffix.loadedData p | .twiddle=>tableData | .output=>outputData | .work=>workData

/-- Real source state following instruction22. Every numerical field comes
from the actual recursive Call and the independently proved certificate. -/
structure Ready {F : Type} (before after : State F) (p : InputLoader.Profile) (certificate : Certificate p)
    (nId owner pointerBase status jId : Nat) (objects ids : Role→Nat)
    (tableData oldWork outputData workData : Nat→Nat) : Prop where
  distinct : Function.Injective objects
  full : FullMainLocals after p.grid nId owner objects ids pointerBase status
  loader : Locals after InputLoader.parameterName InputLoader.parameterType (MainSuffix.loaderIds nId ids jId) owner
    (InputLoader.parameterValues ⟨p,objects .data⟩ p.count)
  arrays : ∀r,WordArrayRep after (objects r) (MainAllocation.length p.grid r)
    (roleData p tableData outputData workData r)
  post : CallPost (buffers p objects distinct) (exponent p) 0 0 1
    (MainSuffix.loadedData p) tableData (fun _=>0) oldWork before after outputData workData
  cells : RecursiveSource.cells outputData 0 p.grid=certificate.output
  outputDigits : ∀k,k<p.grid → ∀d,d<5 → outputData (k*12+d)<1000000000
  outputValues : ∀k,k<p.grid → (ComplexSource.pair outputData (k*12)).1=(certificate.output.getD k (0,0)).1
  outputSmall : ∀k,k<p.grid → (certificate.output.getD k (0,0)).1.natAbs≤400*10^36
  totalZero : ∀d,d<6 → workData (192+d)=0
  quadZero : ∀d,d<6 → workData (208+d)=0
  scope : after.scope=owner
  well : WellScoped after

/-- The exact source status assignment around the complete verified recursive
Call. All allowed argument/operand orders and all source Call results agree. -/
theorem execute {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : Certificate p)
    {before : State F} {nId owner pointerBase status jId : Nat}
    {objects ids : Role→Nat} {tableData oldWork : Nat→Nat}
    (front : MainSuffix.FrontReady before p nId owner objects ids pointerBase status jId tableData oldWork) :
    ∃after outputData workData,NormalSegment context before [statement] after ∧
      Ready before after p certificate nId owner pointerBase status jId objects ids tableData oldWork outputData workData := by
  obtain ⟨after,outputData,workData,called,post,cellsEq,every⟩:=call_from_front context p pinned certificate front
  have fullAfter:=locals_after_recursive front post front.full
  have loaderAfter:=locals_after_recursive front post front.loader
  have args:=source_arguments context front.full
  have actual:=StatusCall.assignment_execution (front.full.lookup none) (fullAfter.lookup none)
    (front.full.slots none) (fullAfter.slots none) args called
  have all : ∀other flow,Exec context before statement flow other → flow=.normal ∧ other=after := by
    intro other flow run
    exact StatusCall.assignment_every_execution (front.full.lookup none) (fullAfter.lookup none)
      (front.full.slots none) (fullAfter.slots none) source_arguments_pure args every run
  have certificateEq : RecursiveSource.cells outputData 0 (2^exponent p)=certificate.output := by
    rw [←grid_power];exact cellsEq
  have normBound : ∀k,k<2^exponent p → ‖FFT.IntegerModel.decode (certificate.output.getD k (0,0))‖≤400 := by
    intro k hk;exact certificate.output_norm k (by rwa [←grid_power] at hk)
  obtain ⟨digits,values,small⟩:=post.output_sum_fields certificateEq normBound
  refine ⟨after,outputData,workData,.single actual all,
    ⟨front.distinct,fullAfter,loaderAfter,?_,post,cellsEq,?_,?_,?_,?_,?_,
      post.frame.scope.trans front.scope,post.frame.frame.well⟩⟩
  · intro r
    cases r with
    | data=>exact post.arrays .input
    | twiddle=>exact post.arrays .twiddle
    | output=>exact post.arrays .output
    | work=>exact post.arrays .work
  · simpa only [←grid_power] using digits
  · simpa only [←grid_power] using values
  · simpa only [←grid_power] using small
  · intro d hd
    rw [post.workOutside (192+d) (by change 192+d<512;omega) (by omega) (by omega)]
    exact front.accumulatorsZero _ (by omega) (by omega)
  · intro d hd
    rw [post.workOutside (208+d) (by change 208+d<512;omega) (by omega) (by omega)]
    exact front.accumulatorsZero _ (by omega) (by omega)

theorem Ready.partialSum_receipt {F : Type} {before after : State F} {p : InputLoader.Profile}
    {certificate : Certificate p} {nId owner pointerBase status jId : Nat} {objects ids : Role→Nat}
    {tableData oldWork outputData workData : Nat→Nat}
    (ready : Ready before after p certificate nId owner pointerBase status jId objects ids tableData oldWork outputData workData)
    (totalAbs : Nat) (receipt : FFT.IntegerModel.absSum certificate.output=totalAbs) :
    OutputSumSource.partialSum (fun k=>certificate.output.getD k (0,0)) p.grid=totalAbs := by
  have length : certificate.output.length=p.grid := by
    rw [←ready.cells];exact cells_length _ _ _
  rw [←length]
  exact (partialSum_getD certificate.output).trans receipt

#print axioms execute
#print axioms Ready.partialSum_receipt
end RH080Next.FFTPV.MainRecursiveStatement
