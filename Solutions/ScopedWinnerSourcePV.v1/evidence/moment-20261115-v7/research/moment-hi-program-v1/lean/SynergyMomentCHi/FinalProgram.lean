/- Two actual source-linked statistics feed the stronger complete ANT consumer.
The same physical reads also supply an entire future family from one output pair. -/
import SynergyMomentCHi.ReadConsumer
import SynergyMomentCHi.ObservedOutput
namespace SynergyMomentCHi.FinalProgram
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
open SynergyAnalytic SynergyAnalytic.HeightPoint
open IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section

def Scenario (kind : Kind) (platform : WorldIO.Platform) (initial : Stream)
 (trace : Nat→Stream) (final : WorldIO.World) : Prop :=
 trace 0=initial ∧
 WorldSource.SourceCall SynergyC.Header.layout (code kind) platform CompleteIOModel.policy
  3 "__wrap_main" [] ⟨Initialization.initializeBoundGlobals.getD Machine.empty,initial⟩
  (WorldIO.signed32 0) ⟨FullMainPrefix.cache,final.stream⟩ ∧
 ReadConsumer.Read kind (ObservedOutput.total kind) ∧
 final.stream.accepted=(trace 768).accepted++ObservedOutput.bytes kind ∧
 final.stream.delivered=final.stream.accepted.length

theorem scenario (kind : Kind) (platform : WorldIO.Platform) (initial : Stream) :
 ∃ trace final,Scenario kind platform initial trace final := by
 obtain ⟨trace,final,out,first,source,read,bytes,delivered⟩:=CompleteProgram.complete kind platform initial
 have same : out=ObservedOutput.total kind :=
  (CompleteProgram.read_identity kind read).trans (ObservedOutput.total_exact kind)
 subst out
 refine ⟨trace,final,first,source,read,?_,delivered⟩
 rw [ObservedOutput.bytes_exact kind]
 simpa only [List.append_assoc] using bytes

theorem source_pi_psi_and_future
 (platform : WorldIO.Platform) (initial : Stream)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 ∃ massTrace massFinal momentTrace momentFinal,
  Scenario .mass platform initial massTrace massFinal ∧
  Scenario .firstMoment platform initial momentTrace momentFinal ∧
  (HasPowerLogBound Eπ (8848544/1000000000) 0 (7/8) (_root_.Real.exp 300) ∧
   HasPowerLogBound Eψ (8848544/1000000000) 0 (7/8) (_root_.Real.exp 300)) ∧
  (∀ L : ℝ,330 ≤ L→HasPowerLogBound Eπ (finitePNTCoefficient
   (momentEnvelope SynergyMomentMath.PNT300.massUpper SynergyMomentMath.PNT300.momentUpper L) L)
   0 (7/8) (_root_.Real.exp L)) := by
 obtain ⟨massTrace,massFinal,massScenario⟩:=scenario .mass platform initial
 obtain ⟨momentTrace,momentFinal,momentScenario⟩:=scenario .firstMoment platform initial
 have massRead:=massScenario.2.2.1
 have momentRead:=momentScenario.2.2.1
 have ant:=ReadConsumer.pi_psi_300 massRead momentRead h hCHJ hrvm hsmall hlow hRH hQRH
 refine ⟨massTrace,massFinal,momentTrace,momentFinal,massScenario,momentScenario,ant,?_⟩
 intro L future
 exact ReadConsumer.future_pi massRead momentRead future h hCHJ hrvm hsmall hlow hRH hQRH
#print axioms scenario
#print axioms source_pi_psi_and_future
end
end SynergyMomentCHi.FinalProgram
