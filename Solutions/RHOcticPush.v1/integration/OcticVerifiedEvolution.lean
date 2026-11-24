/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticSourceEvolution
import OcticFinalSourceConsumer
import OcticOptimizedCertified
import GoldbachTripleCount
import IEANTN.Nodes.BPTOffOrdinate.v1.Conclusions
import IEANTN.Nodes.PrimeKernelInputs.v4.Conclusions
import IEANTN.Nodes.PrimeInterval.v4.Conclusions
import IEANTN.Nodes.PrimeQuantile.v3.Conclusions
import IEANTN.Nodes.Goldbach.v2.Conclusions

/-! Additive final source-verified mathematical edges. The numerical leaves are
ordinary kernel interval proofs, not source-first program verification. Every
original external mathematical source remains explicit; moment caps do not. -/
open Real Set
set_option maxHeartbeats 0
namespace PrimeKernelInputs.v4

theorem challenge_octic_215_zero_estimate (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : octic_215_zero_estimate :=
  RHOcticPush.Final.zero_estimate_215 hn hb

theorem challenge_octic_family_zero_estimate (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : octic_family_zero_estimate :=
  RHOcticPush.Final.zero_estimate_family hn hb

theorem challenge_optimized_215_zero_estimate (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : optimized_215_zero_estimate :=
  RHOcticPush.OptimizedFinal.zero_estimate_215 hn hb

theorem challenge_optimized_family_zero_estimate (hn : Nicolas.v1.spectral_bound)
    (hb : BPTOffOrdinate.v1.bound) : optimized_family_zero_estimate :=
  fun _ hC => RHOcticPush.OptimizedFinal.zero_estimate_family hn hb hC
end PrimeKernelInputs.v4

namespace PrimeInterval.v4
open RHLimit.OcticPrimePowers RHLimit.OcticGeometry

theorem challenge_count_215 (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (hz : PrimeKernelInputs.v4.octic_215_zero_estimate) : count_215 :=
  RHLimit.OcticTwoInputs.prime_count_215 rh he hz

theorem challenge_count_family (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (hz : PrimeKernelInputs.v4.octic_family_zero_estimate) : count_family :=
  RHLimit.OcticTwoInputs.prime_count_family rh he hz

theorem challenge_optimized_strict_215 (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (hz : PrimeKernelInputs.v4.optimized_215_zero_estimate) : optimized_strict_215 := by
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 (43/20) (18203/10000) (1457/1000)
    (3/125) (31/2000) (1/1000) (29/5) rh he hz primepower_cost_215 trivial_cost_215
    RHOcticPush.OptimizedFinal.scalar_geometry_215 forward_coverage_215
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  exact h

theorem challenge_optimized_strict_family (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (hz : PrimeKernelInputs.v4.optimized_family_zero_estimate) : optimized_strict_family := by
  intro C hC u hu
  have h := RHLimit.OcticStrict.open_count_from_kernel 4 C (18203/10000) (1457/1000)
    (3/20) (29/500) (1/1000) (21/5) rh (he C hC) (hz C hC)
    (primepower_cost_family 4 hC) (trivial_cost_family 4 hC)
    (RHOcticPush.OptimizedFinal.scalar_geometry_family hC) (forward_coverage_family hC)
  norm_num [EvenKernel.countCoefficient, EvenKernel.mass] at h
  convert h u hu using 1 <;> first | rfl | ring

theorem challenge_optimized_count_215 (hi : optimized_strict_215) :
    optimized_count_215 := by
  intro u hu
  have hu0 : 0 ≤ u := (exp_pos 24).le.trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 24)).trans hu
  have hlog : 0 ≤ log u := Real.log_nonneg hu1
  have hab : u ≤ u + (43/20)*sqrt u*log u := le_add_of_nonneg_right (by positivity)
  exact (hi u hu).trans_le (QuarticWindow.count_le_primeCounting_difference hu0 hab)

theorem challenge_strict_214891875 (hi : optimized_strict_family) :
    strict_214891875 := by
  have h := hi (343827/160000) (by norm_num)
  norm_num at h
  exact h

theorem challenge_strict_2149_uniform (hi : optimized_strict_family) :
    strict_2149_uniform := by
  have h := hi (2149/1000) (by norm_num)
  norm_num at h
  exact h
theorem challenge_optimized_count_family (hi : optimized_strict_family) :
    optimized_count_family := by
  intro C hC u hu
  have hu0 : 0 ≤ u := (exp_pos 24).le.trans hu
  have hu1 : 1 ≤ u := (Real.one_le_exp_iff.mpr (by norm_num : (0:ℝ) ≤ 24)).trans hu
  have hlog : 0 ≤ log u := Real.log_nonneg hu1
  have hab : u ≤ u + C*sqrt u*log u := le_add_of_nonneg_right
    (mul_nonneg (mul_nonneg (by linarith [hC.1]) (sqrt_nonneg _)) hlog)
  exact (hi C hC u hu).trans_le (QuarticWindow.count_le_primeCounting_difference hu0 hab)
end PrimeInterval.v4

namespace PrimeQuantile.v3

theorem challenge_octic_block (hi : PrimeInterval.v4.count_215) : octic_block :=
  RHContinuation.Network.octic_block hi

theorem challenge_successive_cubes (hi : PrimeInterval.v4.count_215) : successive_cubes :=
  RHContinuation.Network.successive_cubes hi
theorem challenge_optimized_octic_block (hi : PrimeInterval.v4.optimized_count_215) :
    optimized_octic_block := by
  intro u hu m hm
  have hup : 0 < u := (exp_pos 24).trans_le hu
  have hul : 0 ≤ log u := Real.log_nonneg
    ((Real.one_le_exp (by norm_num : (0:ℝ) ≤ 24)).trans hu)
  apply RHContinuation.PrimeQuantiles.quantile_from_count hup.le
    (le_add_of_nonneg_right (by positivity))
  exact hm.trans_lt (hi u hu)
end PrimeQuantile.v3

namespace Goldbach.v2

theorem challenge_octic_sorted_count (hi : PrimeInterval.v4.strict_214891875) :
    octic_sorted_count := by
  intro H n hEven hn hnH hu hwidth
  have hnH' : 2*(H:ℝ)<n := by exact_mod_cast hnH
  have hcount := hi ((n:ℝ)-H) hu
  have hcard := RHOcticPush.Goldbach.window_card_le_sortedTriples hEven hn
    (u := (n:ℝ)-H)
    (v := (n:ℝ)-H+(343827/160000)*sqrt ((n:ℝ)-H)*log ((n:ℝ)-H))
    (by linarith [Real.add_one_le_exp (24:ℝ)]) (by linarith) (by linarith) (by linarith)
  exact hcount.trans_le (by exact_mod_cast hcard)

theorem challenge_octic_fixed_sorted_count (hi : PrimeInterval.v4.optimized_strict_215) :
    octic_fixed_sorted_count := by
  intro H n hEven hn hnH hu hwidth
  have hnH' : 2*(H:ℝ)<n := by exact_mod_cast hnH
  have hcount := hi ((n:ℝ)-H) hu
  have hcard := RHOcticPush.Goldbach.window_card_le_sortedTriples hEven hn
    (u := (n:ℝ)-H)
    (v := (n:ℝ)-H+(43/20)*sqrt ((n:ℝ)-H)*log ((n:ℝ)-H))
    (by linarith [Real.add_one_le_exp (24:ℝ)]) (by linarith) (by linarith) (by linarith)
  exact hcount.trans_le (by exact_mod_cast hcard)
theorem challenge_octic_sorted_family (hi : PrimeInterval.v4.optimized_strict_family) :
    octic_sorted_family := by
  intro H n hEven hn C hC u hu hhalf hupper hres
  have hcard := RHOcticPush.Goldbach.window_card_le_sortedTriples hEven hn
    (u := u) (v := u+C*sqrt u*log u)
    (by linarith [Real.add_one_le_exp (24:ℝ)]) hhalf hupper hres
  exact (hi C hC u hu).trans_le (by exact_mod_cast hcard)
end Goldbach.v2

namespace RHOcticPush.Network
/-- The actual entire octic branch from three general literature inputs and RH.
No explicit-formula, zero-bound or numerical-cap target is an input. Finite
binary Goldbach and geometric conditions occur explicitly inside its conclusion. -/
theorem fully_derived_octic_network (hg : GreenSmooth.v1.formula)
    (hn : Nicolas.v1.spectral_bound) (hb : BPTOffOrdinate.v1.bound) (rh : RH.v1.hypothesis) :
    PrimeKernelInputs.v4.octic_215_zero_estimate ∧
    PrimeKernelInputs.v4.octic_family_zero_estimate ∧
    PrimeKernelInputs.v4.optimized_215_zero_estimate ∧
    PrimeKernelInputs.v4.optimized_family_zero_estimate ∧
    PrimeInterval.v4.count_215 ∧ PrimeInterval.v4.count_family ∧
    PrimeInterval.v4.optimized_count_215 ∧ PrimeInterval.v4.optimized_strict_215 ∧
    PrimeInterval.v4.optimized_strict_family ∧ PrimeInterval.v4.strict_214891875 ∧
    PrimeInterval.v4.strict_2149_uniform ∧ PrimeQuantile.v3.octic_block ∧
    PrimeQuantile.v3.successive_cubes ∧ Goldbach.v2.octic_sorted_count ∧
    Goldbach.v2.octic_fixed_sorted_count ∧ PrimeInterval.v4.optimized_count_family ∧
    PrimeQuantile.v3.optimized_octic_block ∧ Goldbach.v2.octic_sorted_family := by
  have ef := PrimeKernelInputs.v3.challenge_octic_family_explicit_formula hg hn
  have e := PrimeKernelInputs.v3.challenge_octic_215_explicit_formula hg hn
  have z := PrimeKernelInputs.v4.challenge_octic_215_zero_estimate hn hb
  have zf := PrimeKernelInputs.v4.challenge_octic_family_zero_estimate hn hb
  have zo := PrimeKernelInputs.v4.challenge_optimized_215_zero_estimate hn hb
  have zfo := PrimeKernelInputs.v4.challenge_optimized_family_zero_estimate hn hb
  have ci := PrimeInterval.v4.challenge_count_215 rh e z
  have cf := PrimeInterval.v4.challenge_count_family rh ef zf
  have si := PrimeInterval.v4.challenge_optimized_strict_215 rh e zo
  have sf := PrimeInterval.v4.challenge_optimized_strict_family rh ef zfo
  have sn := PrimeInterval.v4.challenge_strict_214891875 sf
  exact ⟨z,zf,zo,zfo,ci,cf,PrimeInterval.v4.challenge_optimized_count_215 si,si,sf,sn,
    PrimeInterval.v4.challenge_strict_2149_uniform sf,
    PrimeQuantile.v3.challenge_octic_block ci,PrimeQuantile.v3.challenge_successive_cubes ci,
    Goldbach.v2.challenge_octic_sorted_count sn,Goldbach.v2.challenge_octic_fixed_sorted_count si,
    PrimeInterval.v4.challenge_optimized_count_family sf,
    PrimeQuantile.v3.challenge_optimized_octic_block
      (PrimeInterval.v4.challenge_optimized_count_215 si),
    Goldbach.v2.challenge_octic_sorted_family sf⟩
end RHOcticPush.Network
#print axioms RHOcticPush.Network.fully_derived_octic_network
#print axioms PrimeInterval.v4.challenge_optimized_strict_215
#print axioms Goldbach.v2.challenge_octic_sorted_count
