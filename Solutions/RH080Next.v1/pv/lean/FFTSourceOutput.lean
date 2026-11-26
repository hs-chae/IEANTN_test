/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTMainSourceNormCall
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.SourceOutput
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals MainAllocation MainSuffix

def caller : State Unit :=
  {environment:=[],objects:=fun _=>none,nextObject:=0,scope:=0,nextScope:=1,mode:=.host,foreign:=()}

theorem caller_well : WellScoped caller := by
  refine ⟨by decide,?_,?_⟩
  · intro id object present
    cases present
  · intro id object scope present storage
    cases present

def sourceMain : InputLoader.Profile → GoldbachDirect.Function
  | .fap=>FapFFTRecursivePV.main_ast | .w4=>FFTRecursivePV.main_ast

def displayBody (p : InputLoader.Profile) : Stmt := .block [
  .expression (.call "printf" [.literal (.string "%llu\n"),
    .cast .ull (.call (failureSourceFunction (isFap p)).name [.literal (.integer p.grid "ULL")])]),
  .returnValue (some (.literal (.integer 0 "")))]

/-- The unchanged application's actual entry point calls the proved norm
function at its original grid, converts its actual return value and prints
it with the generic unsigned-decimal printf contract, then returns zero.
The generic compiler/stdio/OS/hardware interpretation is outside this theorem. -/
theorem actual_main_body (p : InputLoader.Profile) : (sourceMain p).body=displayBody p := by
  cases p <;> rfl
theorem actual_main_selected (p : InputLoader.Profile) :
    findFunction p.program "main"=some (sourceMain p) := by cases p <;> rfl

theorem actual_printf_cast (n : Nat) (fits : n<2^64) :
    Value.convert .ull (.integer (integer64 n))=some (.integer (integer64 n)) :=
  convert64 n fits

/-- A source-linked non-sentinel modeled numerical output.  The execution
witness is the actual complete numerical Call, not evaluation of a hardcoded
scalar or a certificate checker.  Actual main/printf argument association is
proved here; physical stdout association additionally trusts the documented
generic compiler/runtime/printf/OS/hardware contracts. -/
structure Result (p : InputLoader.Profile) (out : Nat) : Prop where
  sourceSyntax : Correspondence.SourceSyntaxCorresponds p.source p.program
  mainSelected : findFunction p.program "main"=some (sourceMain p)
  mainBody : (sourceMain p).body=displayBody p
  execution : ∃after,Call (memoryContext p.program) (failureSourceFunction (isFap p)).name
    [.integer (integer64 p.grid)] caller (.value (.integer (integer64 out))) after
  fits : out<2^64
  nonSentinel : out≠AnswerSource.sentinel

theorem result_value_eq {p : InputLoader.Profile} {out : Nat}
    (certificate : MainCertificate.Certificate p) (result : Result p out) : out=normAnswer p certificate := by
  obtain ⟨after,actual⟩:=result.execution
  have success : CallResult.value (.integer (integer64 out))≠.value allocationFailureValue := by
    intro bad
    apply result.nonSentinel
    exact congrArg Integer.bits (Value.integer.inj (CallResult.value.inj bad))
  have exactValue:=successful_norm_call (memoryContext p.program) p rfl certificate
    (memoryContext_hasMemory p.program) (memoryContext_sound p.program) caller_well (by rfl) actual success
  exact congrArg Integer.bits (Value.integer.inj (CallResult.value.inj exactValue))

/-- An actual full source execution exists, with every allocation and all
application initialization established by the source proof. The separate
all-Call theorem above covers failure choices; existence is not substituted
for universal correctness. -/
theorem actual_result (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p)
    (nonSentinel : normAnswer p certificate≠AnswerSource.sentinel) :
    Result p (normAnswer p certificate) := by
  refine ⟨p.actual_syntax,actual_main_selected p,actual_main_body p,?_,normAnswer_fits p certificate,nonSentinel⟩
  exact norm_call_exists (memoryContext p.program) p rfl certificate
    (memoryContext_hasMemory p.program) (memoryContext_sound p.program) caller caller_well rfl

#print axioms caller_well
#print axioms actual_main_body
#print axioms actual_main_selected
#print axioms result_value_eq
#print axioms actual_result
end RH080Next.FFTPV.SourceOutput
