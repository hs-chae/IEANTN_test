#!/usr/bin/env python3
"""Emit exact kernel obligations; proposals themselves are never accepted proofs."""
import argparse
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent


def generate():
    j = json.loads((HERE / 'PROPOSAL.json').read_text())
    head = '''import SpectralRamCore
namespace RHOcticPush.SpectralRam
open Real Set Finset IEANTN RamanujanPV.AnalyticTransition
open Ramanujan640 Ramanujan640.AnalyticBarrier RHContinuation.Ramanujan
open RHLimit.Ram620 RHOcticPush.Ram RHOcticPush.Correlated
open RHOcticPush.Spectral076 RHOcticPush.BoxPerron
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
set_option leancert.trust "kernel"
'''
    chunks = [head]
    for i, r in enumerate(j['rows']):
        l, u, a, b, k = (f"({s} : ℝ)" for s in
                          (r['l'], r['u'], r['a'], r['b'], j['K']))
        chunks.append(f'''
lemma lower_{i} : {a} ≤ -88 / 100 + lowerNoMax {l} {u} := by
  unfold lowerNoMax pN p3 q
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma upper_{i} : 68 / 100 + upperPowers ({l} - 1) ≤ {b} := by
  unfold upperPowers highRoot pN
  norm_num only [Finset.sum_range_succ, Nat.factorial, Nat.cast_ofNat, Nat.cast_add,
    Nat.cast_zero, zero_add, Nat.reduceAdd, Nat.reduceMul]
  interval_decide 40 (trust := kernel)

lemma numeric_{i} : ∀ z ∈ Set.Icc {l} {u},
    (1 / 1000 : ℝ) ≤ SpectralRam.numericMargin {k} {a} {b} z := by
  unfold SpectralRam.numericMargin F H Q T budget profile q
  simp_rw [fullBase_explicit]
  certify_bound 60 (trust := kernel)

theorem gap_{i} (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
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
  have h := SpectralRam.actual_margin rh hN hI hTab hL hU
    (by norm_num : 27 ≤ {l}) (by norm_num : {u} ≤ 42) hl hu hcut hcap
    (by norm_num : 0 ≤ {k}) hk ha upper_{i}
  have hn := numeric_{i} z ⟨hl, hu⟩
  rw [SpectralRam.numericMargin_eq (by linarith : z ≠ 0)] at hn
  exact hn.trans h

#print axioms numeric_{i}
#print axioms gap_{i}
''')
    l, u = j['lower_log'], j['upper_log']
    chunks.append(f'''
theorem bridge606 (rh : RiemannHypothesis)
    (hN : NicolasContinuation.SourceNicolas119) (hI : SourceIntegratedPsi)
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
    for i, r in enumerate(j['rows'][:-1]):
        chunks.append(f'''  by_cases h{i} : z ≤ ({r['u']} : ℝ)
  · exact gap_{i} rh hN hI hTab hL hU (by linarith) h{i} hc hp
''')
    chunks.append(f'''  exact gap_{len(j['rows'])-1} rh hN hI hTab hL hU (by linarith) hu hc hp

#print axioms bridge606
end RHOcticPush.SpectralRam
''')
    return ''.join(chunks)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--check', action='store_true')
    a = p.parse_args()
    target, result = HERE / 'SpectralRam606Cells.lean', generate()
    if a.check:
        if target.read_text() != result:
            raise ValueError('Generated obligations changed')
    elif target.exists():
        raise ValueError('Preserve previous source before replacement')
    else:
        target.write_text(result)
    print(json.dumps(dict(status='SOURCE_MATCH' if a.check else 'OBLIGATIONS_WRITTEN',
                         source=target.name, acceptance='actual Lean compilation required')))


if __name__ == '__main__':
    main()
