/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WinnerDensityA.ActualLowerContour
import WinnerDensityA.SourceResult
import WinnerDensityA.TightResult
import WinnerDensityA.ReversResult

namespace WinnerPrimaryRectangle
open Real Set IEANTN
open WinnerOriginalScalars WinnerBetaA.ActualObject WinnerSourceContext WinnerLowerContour
set_option maxHeartbeats 0

/-- Seven shared primary analytic fields. The rectangle field keeps the original
count DIFFERENCE and permits both contour edges to be exceptional. No finite RH,
selected lower-edge extension, new moment, density or prime bound is a field. -/
structure SharedInputs : Prop where
  /-- Hiary Theorem1.1 first sentence, independent low-height input. -/
  lowZeta : ∀ u : ℝ, 0 ≤ u  →  u ≤ 3  → 
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (1461/1000:ℝ)
  /-- KLN Lemma4.1 Eq4.2, actual mollifier with X=T. -/
  mollifierMeanSquare : ∀ T : ℝ, height ≤ T  →  ∀ t>0,
    (∫ u in (0:ℝ)..t,‖mollifier T (vertical (1/2) u)‖^2) ≤ 
      (sourceM1*t+sourceM2*T)*log T
  /-- KLN Lemma4.5 Eq4.13 with beta=2. -/
  sourceSmoothing : ∀ T : ℝ, height ≤ T  →  sourceMoment T (1/2) ≤ 
    (8*(601/5000:ℝ)*exp ((601/5000:ℝ)/(2*T^2)))*
      (∫ x in Ioi 0,WinnerBetaA.Minkowski.gaussianWeight x*scaledCriticalF T x)
  /-- KLN Lemma4.7, exact V from Eqs4.19--4.20. -/
  sourceRightMoment : ∀ T : ℝ, height ≤ T  → 
    sourceMoment T (rightLine T) ≤ sourceRightV eulerMascheroniConstant T*(log T)^2
  /-- KLN2.3+2.9,4.12+4.13 with FKS2.7's C8/2 improvement, BEFORE
  removing the low count or selecting Hstar. The original analytic contract is
  asserted only at regular upper/lower edges; countability is contour avoidance. -/
  sourceRectangle : ∀ sigma : ℝ, (3/4:ℝ) ≤ sigma  →  sigma ≤ 7/8  → 
    ∃ Etop : Set ℝ, Etop.Countable ∧ ∀ T : ℝ, height ≤ T  →  T∉Etop  → 
      ∃ Elower : Set ℝ, Elower.Countable ∧ ∀ h : ℝ,
        height-1<h  →  h<height  →  h∉Elower  → 
        IEANTN.zetaN' sigma T-IEANTN.zetaN' sigma h ≤ 
          rawRectangleBound T sigma (sigma-(851/2500)/log T) (1237/1000)
            (cSevenAt eulerMascheroniConstant h) (sourceCEight eulerMascheroniConstant) T h
  /-- KLN Lemma4.9 proof before all U/V substitution. -/
  sourceUnsmoothing : ∀ sigma T : ℝ, (3/4:ℝ) ≤ sigma  →  sigma ≤ 7/8  →  height ≤ T  → 
    sourceFdiff sigma T ≤ sourceMoment T (shifted sigma T)/(2*WinnerSourceContext.sourceOmega sigma T^2)
  /-- KLN Lemma4.4 Eq4.12 on the actual legal strip. -/
  sourceInterpolation : ∀ sigma T : ℝ, (3/4:ℝ) ≤ sigma  →  sigma ≤ 7/8  →  height ≤ T  → 
    sourceMoment T (shifted sigma T) ≤ 
      sourceMoment T (1/2)^((rightLine T-shifted sigma T)/(rightLine T-1/2))*
      sourceMoment T (rightLine T)^((shifted sigma T-1/2)/(rightLine T-1/2))

structure HPYInputs : Prop where
  shared : SharedInputs
  /-- HPY Theorem1.1, arXiv2207.02366v1, t>=3. -/
  hpyZeta : ∀ u : ℝ, 3 ≤ u  → 
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (309/500)*u^((1:ℝ)/6)*log u

structure ReversInputs : Prop where
  shared : SharedInputs
  /-- Revers Theorem1.1(a), arXiv2602.05614v1, t>=3. -/
  reversZeta : ∀ u : ℝ, 3 ≤ u  → 
    ‖riemannZeta (vertical (1/2) u)‖ ≤ (611/1000)*u^((1:ℝ)/6)*log u

/-- The selected-lower-edge source field is DERIVED, not assumed. -/
theorem SharedInputs.selectedCount (h : SharedInputs) :
    IEANTN.RiemannHypothesisUpTo height  →  ∀ sigma : ℝ,
      (3/4:ℝ) ≤ sigma  →  sigma ≤ 7/8  →  ∃ E : Set ℝ, E.Countable ∧
        ∀ T : ℝ, height ≤ T  →  T∉E  → 
          IEANTN.zetaN' sigma T ≤ 
            ((T-Hstar)*log (1+sourceFdiff sigma T/(T-Hstar))+
              (sourceCSeven eulerMascheroniConstant*((1237/1000:ℝ)-shifted sigma T)+
                sourceCEight eulerMascheroniConstant/2)*log T)/
              (2*Real.pi*(sigma-shifted sigma T)) := by
  intro hRH sigma hs hs'
  obtain ⟨Etop,hEtop,hTop⟩:=h.sourceRectangle sigma hs hs'
  refine ⟨Etop,hEtop,?_⟩
  intro T hT hnot
  have hb:=selected_lower_contour hRH hs hs' hT (hTop T hT hnot)
  simpa only [rawRectangleBound,Hstar,sourceFdiff,shifted,WinnerSourceContext.d] using hb

 theorem HPYInputs.toOriginalInputs (h : HPYInputs) : WinnerSourceContext.OriginalInputs where
  lowZeta:=h.shared.lowZeta
  hpyZeta:=h.hpyZeta
  mollifierMeanSquare:=h.shared.mollifierMeanSquare
  sourceSmoothing:=h.shared.sourceSmoothing
  sourceRightMoment:=h.shared.sourceRightMoment
  sourceCount:=h.shared.selectedCount
  sourceUnsmoothing:=h.shared.sourceUnsmoothing
  sourceInterpolation:=h.shared.sourceInterpolation

 theorem ReversInputs.toReversInputs (h : ReversInputs) : WinnerSourceContext.ReversInputs where
  lowZeta:=h.shared.lowZeta
  reversZeta:=h.reversZeta
  mollifierMeanSquare:=h.shared.mollifierMeanSquare
  sourceSmoothing:=h.shared.sourceSmoothing
  sourceRightMoment:=h.shared.sourceRightMoment
  sourceCount:=h.shared.selectedCount
  sourceUnsmoothing:=h.shared.sourceUnsmoothing
  sourceInterpolation:=h.shared.sourceInterpolation

/-- Full actual prime-error conclusion from original regular rectangle relations. -/
theorem primary_hpy_pi300 (hs : WinnerDensityA.CH2Source) (h : HPYInputs)
    (hRH : RiemannHypothesisUpTo WinnerDensityA.H)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009952 0 (7/8) (exp 300) :=
  WinnerDensityA.source_pi300 hs h.toOriginalInputs hRH hqrh

/-- The second executed certificate uses identical primary inputs. -/
theorem primary_tight_pi300 (hs : WinnerDensityA.CH2Source) (h : HPYInputs)
    (hRH : RiemannHypothesisUpTo WinnerDensityA.H)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009898 0 (7/8) (exp 300) :=
  WinnerDensityA.tight_source_pi300 hs h.toOriginalInputs hRH hqrh

/-- The genuine theorem-input update keeps the seven shared source relations. -/
theorem primary_revers_pi300 (hs : WinnerDensityA.CH2Source) (h : ReversInputs)
    (hRH : RiemannHypothesisUpTo WinnerDensityA.H)
    (hqrh : ZetaZeroFreeHalfPlane (7/8)) :
    HasPowerLogBound Eπ 0.009830 0 (7/8) (exp 300) :=
  WinnerDensityA.revers_source_pi300 hs h.toReversInputs hRH hqrh

#print axioms SharedInputs.selectedCount
#print axioms primary_hpy_pi300
#print axioms primary_tight_pi300
#print axioms primary_revers_pi300
end WinnerPrimaryRectangle
