/- The unchanged actual application entry point, including its real nested
norm call, unsigned cast, printf invocation, return and function-scope exit. -/
import FFTMainIOArguments
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics WordArrays MainAllocation MainSuffix SourceLocals

def caller (initial : IOState := {}) : State IOState :=
  {environment:=[],objects:=fun _=>none,nextObject:=0,scope:=0,nextScope:=1,mode:=.host,foreign:=initial}

def mainEntry (initial : IOState := {}) : State IOState :=
  {(caller initial).enterScope with environment:=[]}

def mainFinish (after : State IOState) (initial : IOState := {}) : State IOState :=
  {after.leaveScope (mainEntry initial).scope (caller initial).environment with scope:=(caller initial).scope}

def zero : Value := .integer ⟨.i32,0⟩

theorem caller_well (initial : IOState) : WellScoped (caller initial) := by
  refine ⟨by change 0<1;decide,?_,?_⟩
  · intro id object present;cases present
  · intro id object scope present storage;cases present

theorem mainEntry_well (initial : IOState) : WellScoped (mainEntry initial) :=
  wellScoped_environment (wellScoped_enter (caller_well initial)) []

def mainStatements (p : InputLoader.Profile) : List Stmt :=
  [.expression (.call "printf" (printfExpressions p)),.returnValue (some (.literal (.integer 0 "")))]

theorem main_body (p : InputLoader.Profile) :
    (SourceOutput.sourceMain p).body=.block (mainStatements p) := by cases p <;> rfl

theorem source_main_call (p : InputLoader.Profile) (initial : IOState)
    {out : Nat} (fit : out<2^64) {normAfter printfAfter : State IOState} {printed : CallResult}
    (normCall : Call (ioContext p.program) (failureSourceFunction (isFap p)).name
      [.integer (integer64 p.grid)] (mainEntry initial) (.value (.integer (integer64 out))) normAfter)
    (printfCall : PrintfCall [.string "%llu\n",.integer (integer64 out)] normAfter printed printfAfter) :
    Call (ioContext p.program) "main" [] (caller initial) (.value zero) (mainFinish printfAfter initial) := by
  have printedValue : ∃value,printed=.value value := by cases printfCall <;> exact ⟨_,rfl⟩
  obtain ⟨value,rfl⟩:=printedValue
  have printfExternal : Call (ioContext p.program) "printf" [.string "%llu\n",.integer (integer64 out)]
      normAfter (.value value) printfAfter := by
    apply Call.external (by cases p <;> rfl) (by rfl : External.printf.name="printf")
    exact Or.inr ⟨rfl,printfCall⟩
  refine Call.internal (statements:=mainStatements p) (value:=zero) (SourceOutput.actual_main_selected p) ?_ ?_ ?_ ?_ rfl
  · exact main_body p
  · cases p <;> rfl
  · apply Body.finish
    · exact .cons (.expression (.call (printf_arguments (ioContext p.program) p fit normCall) printfExternal))
        (.abrupt (.returnSome (.literal (.integer 0 "") _ zero rfl)) (by intro h;cases h))
    · intro label bad;cases bad
  · cases p <;> rfl

/-- A complete successful stdout execution exists. All numerical application
initialization is proved from the empty main entry; generic allocation and I/O
success are choices of execution, not universal assumptions. -/
theorem actual_main_success (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p)
    (initial : IOState) :
    ∃after,
      Call (ioContext p.program) "main" [] (caller initial) (.value zero) after ∧
      after.foreign.stdout=initial.stdout++decimalLF (normAnswer p certificate) ∧
      after.foreign.events=initial.events++[⟨normAnswer p certificate,decimalLF (normAnswer p certificate),true⟩] := by
  obtain ⟨normAfter,actual⟩:=norm_call_exists (memoryOnlyContext p.program) p rfl certificate
    (memoryOnly_hasMemory p.program) (memoryOnly_sound p.program) (mainEntry initial)
    (mainEntry_well initial) rfl
  have frame : normAfter.foreign=initial := call_foreign_frame (memoryOnly_foreign_frame p.program) actual
  have normCall:=memoryOnly_call_in_io actual
  have printfCall:=PrintfCall.success normAfter (normAnswer p certificate) (normAnswer_fits p certificate)
  refine ⟨_,source_main_call p initial (normAnswer_fits p certificate) normCall printfCall,?_,?_⟩
  · simp only [mainFinish,State.leaveScope,emit,frame]
  · simp only [mainFinish,State.leaveScope,emit,frame]

/-- The same preserved main can complete with an actual partial printf failure.
Its source ignores the negative printf result and still returns int zero. -/
theorem actual_main_partial_failure (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p)
    (initial : IOState) (written tail : String)
    (isPrefix : written++tail=decimalLF (normAnswer p certificate))
    (code : Int) (negative : -(2^31)≤code ∧ code<0) :
    ∃after,
      Call (ioContext p.program) "main" [] (caller initial) (.value zero) after ∧
      after.foreign.stdout=initial.stdout++written ∧
      after.foreign.events=initial.events++[⟨normAnswer p certificate,written,false⟩] := by
  obtain ⟨normAfter,actual⟩:=norm_call_exists (memoryOnlyContext p.program) p rfl certificate
    (memoryOnly_hasMemory p.program) (memoryOnly_sound p.program) (mainEntry initial)
    (mainEntry_well initial) rfl
  have frame : normAfter.foreign=initial := call_foreign_frame (memoryOnly_foreign_frame p.program) actual
  have normCall:=memoryOnly_call_in_io actual
  have printfCall:=PrintfCall.failure normAfter (normAnswer p certificate) (normAnswer_fits p certificate)
    written tail isPrefix code negative
  refine ⟨_,source_main_call p initial (normAnswer_fits p certificate) normCall printfCall,?_,?_⟩
  · simp only [mainFinish,State.leaveScope,emit,frame]
  · simp only [mainFinish,State.leaveScope,emit,frame]

end RH080Next.FFTPV.MainIO
