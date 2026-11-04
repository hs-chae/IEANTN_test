/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), integration workstream
-/
import CalibrationPilot.NewA

/-!
# Trust reduction: program A (updated instance) with one native fact instead of seven

`CalibrationPilot.NewA` (unchanged) certifies its sum with seven `native_decide` facts. This
module re-proves the same `certified_sum` with every check reduced by the **kernel**
(`decide +kernel`), except one: decoding the decimal literals of the source into rationals.
`FKS2Scalar.decimal` uses `String.splitOn` and `String.toNat?`, which the kernel does not reduce.
That is the exact first blocking computation, isolated as `decode_check`.

Role of each fact, old → new:
- source match, canonical tokenization: native → kernel;
- input enclosure, input domain: native → kernel (on the decoded rationals);
- load/sum execution, output bits, suffix rounding, final budget: native → kernel;
- literal decoding (`String` → `ℚ`): native, the one remaining fact.
Compiler/runtime/hardware trust is unchanged.
-/

namespace CalibrationPilot.KernelA
open FKS2Scalar FKS2Table4 SumStability ForwardRamanujan CalibrationPilot
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- The seven loaded inputs as exact rationals (binary64 values). -/
def dataQ : List ℚ := [(1/1099511627776),(7378697629483821/151115727451828646838272),(1/1099511627776),(5519305075245545/295147905179352825856),(1/1099511627776),(8417527399863843/2361183241434822606848),(1/1099511627776)]

/-- **The one remaining native fact**: decimal literal decoding. -/
theorem decode_check : NewA.program.inputs.mapM loadLiteral = some dataQ ∧
    loadLiteral NewA.program.scale = some 4096 ∧ loadLiteral NewA.program.fixedOffset = some 0 ∧
    loadLiteral NewA.program.positiveOffset = some 0 := by native_decide

theorem map_getD_of_mapM : ∀ {l : List String} {r : List ℚ},
    l.mapM loadLiteral = some r → l.map (fun s => (loadLiteral s).getD 0) = r
  | [], r, h => by simpa using h
  | a :: t, r, h => by
    rw [List.mapM_cons] at h
    cases ha : loadLiteral a with
    | none => simp [ha] at h
    | some b =>
      cases ht : t.mapM loadLiteral with
      | none => simp [ha, ht] at h
      | some r' =>
        simp [ha, ht] at h
        subst h
        simp [ha, map_getD_of_mapM ht]

theorem data_eq : NewA.data = dataQ := map_getD_of_mapM decode_check.1

def sQ : ℚ := (runSum dataQ 0).getD 0

theorem sumOut_eq : NewA.sumOut = sQ := by
  unfold NewA.sumOut sQ
  rw [data_eq]

theorem source_k : sourceMatchesNamed NewA.actualSource NewA.entry NewA.program = true := by
  decide +kernel

theorem canon_k : (ForwardRamanujan.tokens (renderProgram NewA.program)).isSome = true := by
  decide +kernel

theorem enclosure_k : dataQ.length = 7 ∧ (NewA.targets.sum ≤ 4096 * dataQ.sum) := by
  decide +kernel

theorem domain_k : ∀ r ∈ dataQ, FKS2SumBridge.inputCheck r = true := by decide +kernel

theorem rep_k : RepresentsInput (FKS2SumBridge.sumInitial dataQ) dataQ := by
  unfold RepresentsInput
  decide +kernel

theorem runsum_k : runSum dataQ 0 = some sQ := by decide +kernel

theorem chain_k : chainCheck dataQ 0 sQ = true := by decide +kernel

theorem round_k : round64 (sQ * 4096) = some (sQ * 4096) ∧
    round64 (sQ * 4096 - 0) = some (sQ * 4096) ∧ round64 (sQ * 4096 - 0) = some NewA.out := by
  decide +kernel

theorem addition_k : additionCheck (sQ * 4096) (sQ * 4096) = true ∧
    additionCheck (sQ * 4096 - 0) (sQ * 4096) = true ∧
    additionCheck (sQ * 4096 - 0) NewA.out = true := by decide +kernel

theorem bits_k : finiteBits NewA.outputBits = true ∧
    encodePositiveNormal NewA.out = some NewA.outputBits := by decide +kernel

theorem budget_k : (dataQ.map abs).sum = dataQ.sum ∧ gamma (dataQ.length - 1) < 1 ∧
    0 ≤ forwardError 4096 sQ (1 / 10 ^ 10) dataQ.length ∧
    NewA.out + forwardError 4096 sQ (1 / 10 ^ 10) dataQ.length ≤ NewA.bound := by decide +kernel

theorem out_eq : NewA.out = sQ * 4096 := by decide +kernel

theorem suffix_k : suffix NewA.program sQ = some NewA.out := by
  unfold suffix
  rw [decode_check.2.1, decode_check.2.2.1, decode_check.2.2.2]
  decide +kernel

theorem suffixIEEE_k : SuffixIEEE NewA.program sQ NewA.out :=
  ⟨4096, 0, 0, sQ * 4096, sQ * 4096, decode_check.2.1, decode_check.2.2.1, decode_check.2.2.2,
    additionCheck_sound addition_k.1, additionCheck_sound addition_k.2.1,
    additionCheck_sound addition_k.2.2⟩

theorem execution_k : ExecNamed NewA.actualSource NewA.entry NewA.program NewA.initial NewA.out := by
  have hinit : NewA.initial = FKS2SumBridge.sumInitial dataQ := by
    unfold NewA.initial; rw [data_eq]
  obtain ⟨final, hkernel⟩ := ForwardRamanujan.kernel_from_chain chain_k
    (show dataQ.length ≤ 64 by rw [enclosure_k.1]; norm_num)
  refine ⟨source_k, by decide, by decide, dataQ, sQ, final, decode_check.1, ?_, runsum_k, ?_,
    suffix_k, suffixIEEE_k⟩
  · rw [hinit]; exact rep_k
  · rw [hinit]; exact hkernel

/-- `NewA.certified_sum`, re-proved with one native fact. -/
theorem certified_sum_k : (NewA.targets.sum : ℝ) ≤ (NewA.bound : ℝ) := by
  have hd : ValidInputs dataQ := fun r hr => FKS2SumBridge.inputCheck_sound (domain_k r hr)
  have hn : 1 ≤ dataQ.length ∧ dataQ.length ≤ 64 := by rw [enclosure_k.1]; norm_num
  have hg : (gamma (dataQ.length - 1) : ℝ) < 1 := by exact_mod_cast budget_k.2.1
  have href : (NewA.targets.sum : ℝ) ≤ ((4096 : ℚ) : ℝ) * (dataQ.sum : ℝ) := by
    exact_mod_cast enclosure_k.2
  have hf : |(NewA.out : ℝ) - (((4096 : ℚ) : ℝ) * (sQ : ℝ) - ((0 : ℚ) : ℝ) - ((0 : ℚ) : ℝ))| ≤
      ((1 / 10 ^ 10 : ℚ) : ℝ) := by
    rw [out_eq]
    push_cast
    rw [show (sQ : ℝ) * 4096 - (4096 * sQ - 0 - 0) = 0 by ring, abs_zero]
    norm_num
  have h := source_linked_upper (to_exec execution_k canon_k) decode_check.1 runsum_k suffix_k hn hd
    budget_k.1 hg (by norm_num) href hf
  have hb : (NewA.out : ℝ) + (forwardError 4096 sQ (1 / 10 ^ 10) dataQ.length : ℝ) ≤
      (NewA.bound : ℝ) := by exact_mod_cast budget_k.2.2.2
  simp only [Rat.cast_zero, sub_zero] at h
  exact h.trans hb
end CalibrationPilot.KernelA
