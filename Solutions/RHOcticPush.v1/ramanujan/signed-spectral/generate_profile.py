#!/usr/bin/env python3
"""Generate an additive typed-profile consumer; accepted sources are never edited."""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def generate():
    core = (HERE/'SpectralRamCore.lean').read_bytes()
    if hashlib.sha256(core).hexdigest() != 'd4960183293988707bef3cc1bb9ee69f5e9fe6ec378efcbf3e3ce8d600cdcf35':
        raise ValueError('Frozen analytic source changed')
    src = core.decode()
    start = src.index('    (hTab :', src.index('theorem actual_margin'))
    end = src.index('noncomputable def numericMargin')
    body = src[start:end]
    old = 'have hpair := actual_pair rh hN hI'
    if body.count(old) != 1:
        raise ValueError('Expected exact original pair-use site')
    body = body.replace(old, 'have hpair := actual_pair_of_profile hE')
    chunks = ['''import SpectralRam606Cells
import IEANTN.Nodes.RHPrimeCounting.v5.Conclusions

/-! A genuine new typed network edge: actual compensation profile to a local
Ramanujan gap. No source theorem, RH or desired Ramanujan conclusion is hidden
in the consumer. Its compensation input is supplied by the separate signed
Perron/Nicolas proof. Frozen original and earlier synthesis sources are retained.
-/
namespace RHOcticPush.SpectralRam
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram RHOcticPush.Correlated
open RHOcticPush.Spectral076 RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

theorem actual_pair_of_profile (hE : RHPrimeCounting.v5.compensation_profile)
    {k z : ℝ} (hk : 0 ≤ k) (hz : 25 ≤ z) :
    k * GM.error (exp z) - exp 1 * GM.error (exp (z - 1)) ≤ budget k z := by
  have hx := hE (exp z) (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z))
  have hy := hE (exp (z - 1)) (Real.exp_le_exp.mpr (by linarith : (24 : ℝ) ≤ z - 1))
  change |GM.error (exp z)| ≤ Spectral076.profile (log (exp z)) at hx
  change |GM.error (exp (z - 1))| ≤ Spectral076.profile (log (exp (z - 1))) at hy
  simp only [Real.log_exp] at hx hy
  have hxu := (le_abs_self (GM.error (exp z))).trans hx
  have hyl := (neg_le_abs (GM.error (exp (z - 1)))).trans hy
  have h1 := mul_le_mul_of_nonneg_left hxu hk
  have h2 := mul_le_mul_of_nonneg_left hyl (Real.exp_pos 1).le
  unfold budget
  linarith

theorem actual_margin_from_profile (hE : RHPrimeCounting.v5.compensation_profile)
''', body]
    j = json.loads((HERE/'PROPOSAL.json').read_text())
    for i, r in enumerate(j['rows']):
        l,u,a,b,k = (f'({s} : ℝ)' for s in (r['l'],r['u'],r['a'],r['b'],j['K']))
        chunks.append(f'''
theorem profile_gap_{i} (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hl : {l} ≤ z) (hu : z ≤ {u})
    (hcut : (480000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : {k} ≤ 2 * pN 20 {u} := by
    norm_num [pN, Finset.sum_range_succ, Nat.factorial]
  have ha := lower_{i}.trans (by
    linarith [lowerNoMax_le {l} {u}] :
      -88 / 100 + lowerNoMax {l} {u} ≤ -88 / 100 + lowerPowers {l} {u})
  have h := actual_margin_from_profile hE hTab hL hU
    (by norm_num : 27 ≤ {l}) (by norm_num : {u} ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ {k}) hk ha upper_{i}
  have hn := numeric_{i} z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h
''')
    l,u=j['lower_log'],j['upper_log']
    chunks.append(f'''
theorem bridge606_from_profile (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hcut : (606000000000 : ℝ) ≤ exp z) (hcap : exp z ≤ 610000000000) :
    (1 / 1000 : ℝ) ≤ RamStudy.RG (exp z) := by
  have hlo : exp ({l} : ℝ) ≤ (606000000000 : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hup : (610000000000 : ℝ) ≤ exp ({u} : ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : ({l} : ℝ) ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ ({u} : ℝ) := exp_le_exp.mp (hcap.trans hup)
  have hc : (480000000000 : ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000 : ℝ) := by linarith
''')
    for i,r in enumerate(j['rows'][:-1]):
        chunks.append(f'''  by_cases h{i} : z ≤ ({r['u']} : ℝ)
  · exact profile_gap_{i} hE hTab hL hU (by linarith) h{i} hc hp
''')
    chunks.append(f'''  exact profile_gap_{len(j['rows'])-1} hE hTab hL hU (by linarith) hu hc hp

theorem local_actual_gap (hE : RHPrimeCounting.v5.compensation_profile)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{x : ℝ}} (hx : (606000000000 : ℝ) ≤ x) (hu : x ≤ (610000000000 : ℝ)) :
    (1 / 1000 : ℝ) * x^2 / (log x)^6 ≤ RamanujanGap.v1.gap x := by
  have hx0 : 0 < x := by linarith
  have hr := bridge606_from_profile hE hTab hL hU (z := log x)
    (by simpa only [exp_log hx0] using hx) (by simpa only [exp_log hx0] using hu)
  rw [exp_log hx0] at hr
  have hl : 0 < log x := log_pos (by linarith)
  have hp : 0 < log x^6 / x^2 := by positivity
  have he : (log x^6 / x^2) * ((1 / 1000 : ℝ) * x^2 / (log x)^6) = 1 / 1000 := by
    field_simp [hx0.ne', hl.ne']
  apply (mul_le_mul_iff_right₀ hp).mp
  rw [he]
  exact hr

#print axioms actual_pair_of_profile
#print axioms actual_margin_from_profile
''')
    for i in range(len(j['rows'])):
        chunks.append(f'#print axioms profile_gap_{i}\n')
    chunks.append('''#print axioms bridge606_from_profile
#print axioms local_actual_gap
end RHOcticPush.SpectralRam
''')
    return ''.join(chunks)


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check',action='store_true')
    a=p.parse_args()
    target,result=HERE/'SpectralRamProfile.lean',generate()
    if a.check:
        if target.read_text()!=result:raise ValueError('Generated profile consumer changed')
    elif target.exists():raise ValueError('Preserve previous generated source')
    else:target.write_text(result)
    print(json.dumps(dict(status='SOURCE_MATCH' if a.check else 'OBLIGATIONS_WRITTEN',
                         acceptance='actual Lean proof required')))


if __name__=='__main__':main()
