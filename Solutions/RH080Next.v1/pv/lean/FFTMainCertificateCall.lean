import FFTMainCertificateBase
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainCertificate
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame RecursiveSource MainRootBirth

theorem front_buffer_arrays {F : Type} {state : State F} {p : InputLoader.Profile}
    {nId owner pointerBase status jId : Nat} {objects ids : MainAllocation.Role→Nat}
    {tableData workData : Nat→Nat}
    (front : MainSuffix.FrontReady state p nId owner objects ids pointerBase status jId tableData workData) :
    ∀r,WordArrayRep state ((buffers p objects front.distinct).object r)
      ((buffers p objects front.distinct).length r)
      (bufferData (MainSuffix.loadedData p) tableData (fun _=>0) workData r) := by
  intro r
  cases r with
  | input=>exact front.dataArray
  | output=>exact front.output
  | twiddle=>exact front.table
  | work=>exact front.work

/-- The genuine recursive Call on genuine front-state buffers, consuming only
the independently kernel-proved mathematical certificate. Every actual Call
agrees; observed application output is never a premise. -/
theorem call_from_front {F : Type} (context : Context F) (p : InputLoader.Profile)
    (pinned : context.program=p.program) (certificate : Certificate p)
    {before : State F} {nId owner pointerBase status jId : Nat}
    {objects ids : MainAllocation.Role→Nat} {tableData workData : Nat→Nat}
    (front : MainSuffix.FrontReady before p nId owner objects ids pointerBase status jId tableData workData) :
    ∃after output work,Call context "fft_recursive"
        (arguments (objects .output) (objects .data) (objects .twiddle) (objects .work)
          0 0 1 p.grid p.grid) before (.value (.integer (integer64 0))) after ∧
      CallPost (buffers p objects front.distinct) (exponent p) 0 0 1
        (MainSuffix.loadedData p) tableData (fun _=>0) workData before after output work ∧
      cells output 0 p.grid=certificate.output ∧
      ∀other result,Call context "fft_recursive"
        (arguments (objects .output) (objects .data) (objects .twiddle) (objects .work)
          0 0 1 p.grid p.grid) before result other →
        result=.value (.integer (integer64 0)) ∧ other=after := by
  obtain ⟨snapshot,tableView⟩:=front.tableSnapshot
  have view : TwiddleSource.View snapshot (objects .twiddle) (objects .work) (2^exponent p)
      (TwiddleSource.combinedIds (MainSuffix.tableOldIds nId ids pointerBase status) jId) owner
      ((2^exponent p)/2) tableData workData (FFT.IntegerModel.root p.grid) := by
    simpa only [←grid_power] using tableView
  have tableLength : ((FFT.IntegerModel.unit,0)::certificate.rest).length=(2^exponent p)/2 := by
    rw [←grid_power];exact certificate.length
  have inputEq : ∀j,j<2^exponent p → cell (MainSuffix.loadedData p) j=p.mathematicalInput j := by
    intro j bound
    exact front.inputPair j (by rwa [←grid_power] at bound)
  have mass : FFT.coefficientMass (2^exponent p) (fun j=>FFT.IntegerModel.decode (p.mathematicalInput j))≤362 := by
    rw [←grid_power];exact certificate.mass
  obtain ⟨after,output,work,called,post,cellsEq,every⟩:=source_certificate_recursive_total context
    (helpers context p pinned) (buffers p objects front.distinct) (MainSuffix.loadedData p) tableData
    (grid_power p) (by cases p <;> decide) (by cases p <;> decide)
    (loaded_normalized p) view certificate.twiddles tableLength certificate.stages p.mathematicalInput
    certificate.chains inputEq mass certificate.stageError certificate.output certificate.trace
    before (fun _=>0) workData front.well (front_buffer_arrays front)
  refine ⟨after,output,work,?_,post,?_,?_⟩
  · simpa only [←grid_power,buffers,bufferRole] using called
  · simpa only [←grid_power] using cellsEq
  · intro other result run
    exact every other result (by simpa only [←grid_power,buffers,bufferRole] using run)

#print axioms front_buffer_arrays
#print axioms call_from_front
end RH080Next.FFTPV.MainCertificate
