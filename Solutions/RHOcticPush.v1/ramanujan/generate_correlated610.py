#!/usr/bin/env python3
"""Emit exact whole-interval Lean goals for the signed GM consumer."""
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent


def generate():
    data = json.loads((HERE / 'CORRELATED_610_SCOUT.json').read_text())
    files = {}
    for i, row in enumerate(data['rows']):
        l, u, a, b = [f"({row[k]}:ℝ)" for k in ['l', 'u', 'a', 'b']]
        k = '(' + data['K'] + ':ℝ)'
        text = f'''import CorrelatedNumeric
namespace RHOcticPush.Correlated
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"

lemma lower610_{i} : {a} ≤ -88/100+lowerNoMax {l} {u} := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper610_{i} : 68/100+upperPowers ({l}-1) ≤ {b} := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 40 (trust := kernel)

/-- Certified for EVERY real parameter in this closed interval. -/
lemma numeric610_{i} : ∀ z ∈ Set.Icc {l} {u},
    (1/1000:ℝ) ≤ numericMargin {k} {a} {b} z := by
  unfold numericMargin F H Q T numericBudget q
  simp_rw [fullBase_explicit]
  certify_bound 40 (trust := kernel)

theorem gap610_{i} (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hTab : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hl : {l} ≤ z) (hu : z ≤ {u})
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    (1/1000:ℝ) ≤ RamStudy.RG (exp z) := by
  have hk : {k} ≤ 2*pN 20 {u} := by
    norm_num [pN,Finset.sum_range_succ,Nat.factorial]
  have ha := lower610_{i}.trans (by
    linarith [lowerNoMax_le {l} {u}] :
      -88/100+lowerNoMax {l} {u} ≤ -88/100+lowerPowers {l} {u})
  have h := actual_margin hRH hGM hP hJ hTab hL hU
    (by norm_num : 27 ≤ {l}) (by norm_num : {u} ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ {k})
    (by interval_decide 40 (trust := kernel) : {k} ≤ exp 1) hk ha upper610_{i}
  have hn := numeric610_{i} z ⟨hl,hu⟩
  rw [numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric610_{i}
#print axioms gap610_{i}
end RHOcticPush.Correlated
'''
        files['Corr610Cell' + str(i) + '.lean'] = text
    return files


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    files = generate()
    for name, text in files.items():
        path = HERE/name
        if a.check:
            if not path.exists() or path.read_text() != text:
                raise ValueError('Generated source drift: ' + name)
        else:
            path.write_text(text)
    print(json.dumps({'status': 'GOALS_MATCH' if a.check else 'GOALS_GENERATED',
                      'modules': sorted(files), 'acceptance': 'Separate Lean kernel compilation'}))


if __name__ == '__main__':
    main()
