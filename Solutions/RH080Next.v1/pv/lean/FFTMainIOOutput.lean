/- Source-first output witness with the full operational main Call. -/
import FFTMainIOAssociation
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section
namespace RH080Next.FFTPV.MainIO
open GoldbachDirect GoldbachDirect.Semantics WordArrays MainAllocation MainSuffix

/-- A successful complete main execution and its actual final generic printf
event. Neither initialized application arrays nor correct output are assumed.
Failure executions remain covered separately by every_main_call. -/
structure Result (p : InputLoader.Profile) (out : Nat) : Prop where
  sourceSyntax : Correspondence.SourceSyntaxCorresponds p.source p.program
  execution : ∃after,Call (ioContext p.program) "main" [] (caller {}) (.value zero) after ∧
    after.foreign.stdout=decimalLF out ∧
    after.foreign.events.getLast?=some ⟨out,decimalLF out,true⟩
  fits : out<2^64
  nonSentinel : out≠AnswerSource.sentinel

theorem result_value_eq {p : InputLoader.Profile} {out : Nat}
    (certificate : MainCertificate.Certificate p) (result : Result p out) : out=normAnswer p certificate := by
  obtain ⟨after,actual,_,lastEvent⟩:=result.execution
  obtain ⟨_,n,normAfter,printfAfter,printfResult,fit,alternatives,_,api,finished⟩:=
    every_main_call p certificate {} actual
  rw [finished] at lastEvent
  cases api with
  | success before n fit =>
    have eq : n=out := by
      have event : (PrintEvent.mk n (decimalLF n) true)=⟨out,decimalLF out,true⟩ := by
        simpa [mainFinish,State.leaveScope,emit] using lastEvent
      exact congrArg PrintEvent.argument event
    subst n
    exact alternatives.resolve_left result.nonSentinel
  | failure before n fit written tail isPrefix code negative =>
    simp [mainFinish,State.leaveScope,emit] at lastEvent

theorem actual_result (p : InputLoader.Profile) (certificate : MainCertificate.Certificate p)
    (nonSentinel : normAnswer p certificate≠AnswerSource.sentinel) :
    Result p (normAnswer p certificate) := by
  obtain ⟨after,actual,stdout,events⟩:=actual_main_success p certificate {}
  refine ⟨p.actual_syntax,⟨after,actual,?_,?_⟩,normAnswer_fits p certificate,nonSentinel⟩
  · simpa using stdout
  · simp [events]

end RH080Next.FFTPV.MainIO
