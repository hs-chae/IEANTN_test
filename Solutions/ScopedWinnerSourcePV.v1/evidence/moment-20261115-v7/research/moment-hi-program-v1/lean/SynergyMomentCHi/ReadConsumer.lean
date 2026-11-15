/- Physical total reads supply the actual mass/first-moment numerical providers.
The new ANT conclusions use both read-derived bounds; no unused source-call
conjunct is attached to an old numerical model theorem. -/
import SynergyMomentCHi.CompleteProgram
import SynergyMomentMath.PNTProfile
namespace SynergyMomentCHi.ReadConsumer
open ScopedC ScopedC.Machine ScopedNumerical ScopedIO SynergyHeightC SynergyMomentC
open SynergyBasis SynergyAnalytic SynergyAnalytic.HeightPoint
open IEANTN WinnerOriginalScalars WinnerNewHeightSource WinnerDirectKernel
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 100000
noncomputable section
abbrev Read (kind : Kind) (out : ProofBox) : Prop :=
 evalExpr SynergyC.Header.layout FullMainPrefix.service 1
  (FullMainEdges.loopState (FamilyAPI.total kind 768) 768) (.var "total")=
  some (SynergyC.SourceIntervalMath.represented out,
   FullMainEdges.loopState (FamilyAPI.total kind 768) 768)

theorem mass_interval {out : ProofBox} (read : Read .mass out) :
 RealBox.Contains 128 out (totalMass SynergyMomentMath.Real.mass 768) := by
 have same:=CompleteProgram.read_identity .mass read
 exact Eq.mpr (congrArg (fun box : ProofBox=>
   RealBox.Contains 128 box (totalMass SynergyMomentMath.Real.mass 768)) same)
   SourceMomentSumsV1.Real.mass_interval

theorem moment_interval {out : ProofBox} (read : Read .firstMoment out) :
 RealBox.Contains 128 out
  (firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768) := by
 have same:=CompleteProgram.read_identity .firstMoment read
 exact Eq.mpr (congrArg (fun box : ProofBox=>RealBox.Contains 128 box
   (firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768)) same)
   SourceMomentSumsV1.Real.moment_interval

theorem mass_upper {out : ProofBox} (read : Read .mass out) :
 totalMass SynergyMomentMath.Real.mass 768 ≤ SynergyMomentMath.PNT300.massUpper := by
 have same:=CompleteProgram.read_identity .mass read
 have outputBound : SynergyMomentMath.Real.realWord out.hi ≤ SynergyMomentMath.PNT300.massUpper :=
  Eq.mpr (congrArg (fun box : ProofBox=>SynergyMomentMath.Real.realWord box.hi ≤
    SynergyMomentMath.PNT300.massUpper) same) SourceMomentSumsV1.Real.mass_word_upper
 exact ((le_div_iff₀ (RealBox.scale_real_pos 128)).mpr (mass_interval read).2).trans outputBound

theorem moment_upper {out : ProofBox} (read : Read .firstMoment out) :
 firstMoment SynergyMomentMath.Real.mass SynergyMomentMath.Real.dValue 768 ≤
 SynergyMomentMath.PNT300.momentUpper := by
 have same:=CompleteProgram.read_identity .firstMoment read
 have outputBound : SynergyMomentMath.Real.realWord out.hi ≤ SynergyMomentMath.PNT300.momentUpper :=
  Eq.mpr (congrArg (fun box : ProofBox=>SynergyMomentMath.Real.realWord box.hi ≤
    SynergyMomentMath.PNT300.momentUpper) same) SourceMomentSumsV1.Real.moment_word_upper
 exact ((le_div_iff₀ (RealBox.scale_real_pos 128)).mpr (moment_interval read).2).trans outputBound

theorem pi_psi_300 {massOut momentOut : ProofBox}
 (massRead : Read .mass massOut) (momentRead : Read .firstMoment momentOut)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (8848544/1000000000) 0 (7/8) (_root_.Real.exp 300) ∧
 HasPowerLogBound Eψ (8848544/1000000000) 0 (7/8) (_root_.Real.exp 300) :=
 SynergyMomentMath.PNT300.pi_psi_from_moments (mass_upper massRead) (moment_upper momentRead)
  h hCHJ hrvm hsmall hlow hRH hQRH

theorem future_pi {massOut momentOut : ProofBox}
 (massRead : Read .mass massOut) (momentRead : Read .firstMoment momentOut)
 {L : ℝ} (future : 330 ≤ L)
 (h : PrimaryInputs (3681/10000) (3599/10000))
 (hCHJ : OriginalCHJSource) (hrvm : ZeroCount.v1.rvm_error_bound)
 (hsmall : ZeroCount.v1.rvm_error_small)
 (hlow : LowZeroes.v1.no_zeroes_below_first_ordinate)
 (hRH : RiemannHypothesisUpTo WinnerOriginalScalars.height)
 (hQRH : ZetaZeroFreeHalfPlane (7/8)) :
 HasPowerLogBound Eπ (finitePNTCoefficient (momentEnvelope
  SynergyMomentMath.PNT300.massUpper SynergyMomentMath.PNT300.momentUpper L) L)
  0 (7/8) (_root_.Real.exp L) :=
 SynergyMomentMath.PNTProfile.future_from_moments (mass_upper massRead)
  (moment_upper momentRead) future h hCHJ hrvm hsmall hlow hRH hQRH
#print axioms mass_interval
#print axioms moment_interval
#print axioms mass_upper
#print axioms moment_upper
#print axioms pi_psi_300
#print axioms future_pi
end
end SynergyMomentCHi.ReadConsumer
