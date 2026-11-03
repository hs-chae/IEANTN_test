/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FKS2Pair.GenericMath
import FKS2Table4.Program

namespace FKS2Pair
open FKS2Scalar FKS2Table4 SumStability

/-- Exact selected-file association for the existing supported30-entry constructor. -/
def sourceMatches (src : String) (p : TransportProgram) : Bool :=
  let ts := SumStability.tokens src
  ts.isSome && ts==SumStability.tokens (renderTransport p)

/-- Primitive IEEE nearest-rounding behavior of each actual suffix operation.
These are operational facts, not assumed error allowances. -/
def SuffixIEEE (p : TransportProgram) (s out : ℚ) : Prop :=
  ∃ scale a point tail r0 r1 r2 : ℚ,
    loadLiteral p.scale=some scale ∧ loadLiteral p.anchor=some a ∧
    loadLiteral p.point=some point ∧ loadLiteral p.tail=some tail ∧
    RN64 (s*scale) r0 ∧ RN64 (r0+a) r1 ∧ RN64 (r1+point) r2 ∧ RN64 (r2+tail) out

/-- The source is an argument, not the historic QRH-selected file. No accuracy field. -/
def ExecTransportAt (src : String) (p : TransportProgram) (initial : CState) (out : ℚ) : Prop :=
  sourceMatches src p=true ∧ p.inputs.length=30 ∧
  ∃ xs s final,
    p.inputs.mapM loadLiteral=some xs ∧ RepresentsInput initial xs ∧
    runSum xs 0=some s ∧ ExecC selectedSumProgram initial final s ∧
    runSuffix p s=some out ∧ SuffixIEEE p s out

def initialFor (xs : List ℚ) : CState := FKS2SumBridge.sumInitial xs

theorem kernel_from_chain {xs : List ℚ} {s : ℚ}
    (hc : chainCheck xs 0 s=true) (hn : xs.length ≤ 64) :
    ∃ final, ExecC selectedSumProgram (initialFor xs) final s := by
  have hrun := chain_sound xs 0 s hc
  obtain ⟨last,hl,hout⟩ := FKS2SumBridge.run_to_for hrun (initialFor xs) rfl
    (by simp [initialFor,FKS2SumBridge.sumInitial]) rfl
    (by simp [initialFor,FKS2SumBridge.sumInitial]) hn
  refine ⟨{last with returned := some last.acc},rfl,last,?_,rfl,hout.symm⟩
  simpa [initialized,initialFor,FKS2SumBridge.sumInitial] using hl

theorem output_unique {src : String} {p : TransportProgram} {initial : CState}
    {xs : List ℚ} {s q out : ℚ} (he : ExecTransportAt src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hs : runSuffix p s=some q) : out=q := by
  obtain ⟨_,_,ys,v,final,hy,hrep,hv,hkernel,hout⟩ := he
  have hys : ys=xs := Option.some.inj (hy.symm.trans hl)
  subst ys
  have hvv : v=s := Option.some.inj (hv.symm.trans hr)
  subst v
  exact Option.some.inj (hout.1.symm.trans hs)

/-- Uses the actual indexed-array kernel execution from this source/configuration. -/
theorem sum_upper {src : String} {p : TransportProgram} {initial : CState}
    {xs : List ℚ} {s out : ℚ} (he : ExecTransportAt src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hn : xs.length=30) (hd : ValidInputs xs)
    (habs : (xs.map abs).sum=xs.sum) :
    (xs.sum:ℚ) ≤ (s/(1-gamma 29):ℚ) := by
  obtain ⟨_,_,ys,v,final,hy,hrep,hv,hkernel,hout⟩ := he
  have hys : ys=xs := Option.some.inj (hy.symm.trans hl)
  subst ys
  have hvv : v=s := Option.some.inj (hv.symm.trans hr)
  subst v
  have herr : |(s:ℝ)-(xs.sum:ℚ)| ≤ (gamma 29:ℝ)*((xs.map abs).sum:ℚ) := by
    simpa [hn,exactSum,sumAbs] using c_sum_forward_error_real xs initial final s
      (by rw [hn];norm_num) hd hrep hkernel
  rw [habs] at herr
  have hg : (gamma 29:ℝ)<1 := by norm_num [gamma,u]
  have hs := (abs_le.mp herr).1
  have hreal : (xs.sum:ℚ) ≤ (s:ℝ)/(1-(gamma 29:ℝ)) := by
    apply (le_div_iff₀ (by linarith : (0:ℝ)<1-(gamma 29:ℝ))).mpr
    nlinarith
  exact_mod_cast hreal

def forwardError (scale s eps : ℚ) : ℚ :=
  scale*(s/(1-gamma 29)-s)+eps

/-- Profile enclosures and separately proved suffix errors compose with actual source execution.
The general source-facing summation theorem is consumed by sum_upper, not a detached exact sum. -/
theorem source_linked_transport_upper {U : ℕ → ℝ}
    {src : String} {p : TransportProgram} {initial : CState}
    {xs : List ℚ} {s q out scale a point tail eps : ℚ}
    (he : ExecTransportAt src p initial out)
    (hl : p.inputs.mapM loadLiteral=some xs) (hr : runSum xs 0=some s)
    (hs : runSuffix p s=some q) (hn : xs.length=30) (hd : ValidInputs xs)
    (habs : (xs.map abs).sum=xs.sum) (hscale : 0 ≤ scale)
    (hc : cells U ≤ (scale:ℝ)*(xs.sum:ℚ))
    (ha : anchor U ≤ (a:ℝ)) (hp : U 30 ≤ (point:ℝ))
    (ht : U 30/328 ≤ (tail:ℝ))
    (hf : |(q:ℝ)-((scale:ℝ)*(s:ℝ)+(a:ℝ)+(point:ℝ)+(tail:ℝ))| ≤ (eps:ℝ)) :
    Bsafe U ≤ (out:ℝ)+(forwardError scale s eps:ℝ) := by
  have hsum := sum_upper he hl hr hn hd habs
  have hsumR : (xs.sum:ℝ) ≤ (s:ℝ)/(1-(gamma 29:ℝ)) := by exact_mod_cast hsum
  have hm := mul_le_mul_of_nonneg_left hsumR
    (show (0:ℝ) ≤ (scale:ℝ) by exact_mod_cast hscale)
  have hlo := (abs_le.mp hf).1
  rw [output_unique he hl hr hs]
  unfold Bsafe forwardError
  push_cast
  linarith [hc,ha,hp,ht]
end FKS2Pair
