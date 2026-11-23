#!/usr/bin/env python3
"""Regenerate proposed exact goals; Lean, rather than this script, accepts them."""
from pathlib import Path
import argparse
import json

HERE = Path(__file__).resolve().parent


def generate():
    rows = json.loads((HERE / 'SCOUT_FRONTIER.json').read_text())
    results = {}
    for band in rows['bands']:
        name = band['band']
        local = [r for r in rows['rows'] if r['band'] == name]
        module = 'RamBand' + name.title()
        text = '''import RamPushCore
namespace RHOcticPush.Ram
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option leancert.trust "kernel"
'''
        if name == 'high':
            text += 'set_option Elab.async false\n'
        for i, row in enumerate(local):
            l, u, c, d = [f"({row[k]}:ℝ)" for k in ['l', 'u', 'c', 'd']]
            target = '(' + row['target'] + ':ℝ)'
            key = name + '_' + str(i)
            text += f'''
lemma c_{key} : {c} ≤ -88/100-shift5 {l} {u}+lowerNoMax {l} {u} := by
  unfold shift5 lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma d_{key} : 68/100+shift5 ({l}-1) ({u}-1)+upperPowers ({l}-1) ≤ {d} := by
  unfold shift5 upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

lemma m_{key} : {target} ≤ enhancedMargin {l} {u} {c} {d}+1/1600 := by
  unfold enhancedMargin
  rw [fullBase_explicit]
  unfold pN
  norm_num only [Finset.sum_range_succ,Nat.factorial,Nat.cast_ofNat,Nat.cast_add,
    Nat.cast_zero,zero_add,Nat.reduceAdd,Nat.reduceMul]
  interval_decide 80 (trust := kernel)

theorem gap_{key} (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hl : {l} ≤ z) (hu : z ≤ {u})
    (hcut : (480000000000:ℝ) ≤ exp z) (hcap : exp z ≤ 640000000000) :
    {target} ≤ RamStudy.RG (exp z) := by
  have hc := c_{key}.trans (by
    linarith [lowerNoMax_le {l} {u}] :
      -88/100-shift5 {l} {u}+lowerNoMax {l} {u} ≤
      -88/100-shift5 {l} {u}+lowerPowers {l} {u})
  have hb := actual_deficits5 hRH hGM hP hJ hT hL hU
    (by norm_num : 27 ≤ {l}) (by norm_num : {u} ≤ 42) hl hu hcut hcap hc d_{key}
  exact m_{key}.trans (sharp_enhanced_slab (by norm_num : 27 ≤ {l}) hl hu
    (by norm_num : 0 ≤ {c}) (by norm_num : 0 ≤ {d}) hb.1 hb.2)
'''
        lower = '(' + band['lower_log_endpoint'] + ':ℝ)'
        upper = '(' + band['upper_log_endpoint'] + ':ℝ)'
        target = '(' + band['target'] + ':ℝ)'
        stop_key = str(band['stop'] // 10**9)
        text += f'''
theorem bridge_{name} (hRH : SharedRH.hypothesis) (hGM : GM_Q_Theorem1_1)
    (hP : Buthe.v1.theorem_2_psi) (hJ : Buthe.v1.theorem_2_li_minus_riemann_pi)
    (hT : Buthe.v1.table_1_interval_bounds)
    (hL : Buthe.v1.theorem_2_li_minus_pi) (hU : Buthe.v1.theorem_2_li_gt_pi)
    {{z : ℝ}} (hcut : ({band['start']}:ℝ) ≤ exp z)
    (hcap : exp z ≤ {band['stop']}) : {target} ≤ RamStudy.RG (exp z) := by
  have hlo : exp {lower} ≤ ({band['start']}:ℝ) := by
    interval_decide 80 (trust := kernel)
  have hl : {lower} ≤ z := exp_le_exp.mp (hlo.trans hcut)
  have hu : z ≤ {upper} := by
    have h := (Real.log_le_log (exp_pos z) hcap).trans HighLog.log_{stop_key}
    norm_num only [Real.log_exp] at h
    convert h using 1 <;> norm_num
  have hc : (480000000000:ℝ) ≤ exp z := by linarith
  have hp : exp z ≤ (640000000000:ℝ) := by linarith
'''
        for i, row in enumerate(local[:-1]):
            u = '(' + row['u'] + ':ℝ)'
            text += f'''  by_cases h{i} : z ≤ {u}
  · exact gap_{name}_{i} hRH hGM hP hJ hT hL hU (by linarith) h{i} hc hp
'''
        text += f'''  exact gap_{name}_{len(local)-1} hRH hGM hP hJ hT hL hU
    (by linarith) hu hc hp

#print axioms bridge_{name}
end RHOcticPush.Ram
'''
        results[module + '.lean'] = text
    return results


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    files = generate()
    for name, text in files.items():
        path = HERE / name
        if args.check:
            if not path.is_file() or path.read_text() != text:
                raise ValueError('Generated proof source differs: ' + name)
        else:
            path.write_text(text)
    print(json.dumps({'status': 'GOALS_MATCH' if args.check else 'GOALS_GENERATED',
                      'files': sorted(files), 'kernel_acceptance': 'Separate Lean build required'}))


if __name__ == '__main__':
    main()
