/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ForestFinal
import FFTGlobalTraceBounds

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
noncomputable section
namespace FapForest17
open RH080Next.FFT RH080Next.FFT.IntegerModel

theorem top_table_shape : w17=(unit,0)::w17.tail := by rfl
theorem top_table_length : w17.length=65536 := by decide +kernel
theorem seed_exact : decode seed=rootSeed17 := by
  apply Complex.ext <;> norm_num [seed,decode,unit,rootSeed17]

theorem all_stage_chains : ∀ t<17,
    DecimationTrace (17-(t+1)) w17 (stages (t+1)) := by
  intro t ht
  interval_cases t
  · exact (DecimationTrace.cons 15 w17 w16 w01 decimation16 (DecimationTrace.cons 14 w16 w15 w01 decimation15 (DecimationTrace.cons 13 w15 w14 w01 decimation14 (DecimationTrace.cons 12 w14 w13 w01 decimation13 (DecimationTrace.cons 11 w13 w12 w01 decimation12 (DecimationTrace.cons 10 w12 w11 w01 decimation11 (DecimationTrace.cons 9 w11 w10 w01 decimation10 (DecimationTrace.cons 8 w10 w09 w01 decimation09 (DecimationTrace.cons 7 w09 w08 w01 decimation08 (DecimationTrace.cons 6 w08 w07 w01 decimation07 (DecimationTrace.cons 5 w07 w06 w01 decimation06 (DecimationTrace.cons 4 w06 w05 w01 decimation05 (DecimationTrace.cons 3 w05 w04 w01 decimation04 (DecimationTrace.cons 2 w04 w03 w01 decimation03 (DecimationTrace.cons 1 w03 w02 w01 decimation02 (DecimationTrace.cons 0 w02 w01 w01 decimation01 (DecimationTrace.refl w01)))))))))))))))))
  · exact (DecimationTrace.cons 14 w17 w16 w02 decimation16 (DecimationTrace.cons 13 w16 w15 w02 decimation15 (DecimationTrace.cons 12 w15 w14 w02 decimation14 (DecimationTrace.cons 11 w14 w13 w02 decimation13 (DecimationTrace.cons 10 w13 w12 w02 decimation12 (DecimationTrace.cons 9 w12 w11 w02 decimation11 (DecimationTrace.cons 8 w11 w10 w02 decimation10 (DecimationTrace.cons 7 w10 w09 w02 decimation09 (DecimationTrace.cons 6 w09 w08 w02 decimation08 (DecimationTrace.cons 5 w08 w07 w02 decimation07 (DecimationTrace.cons 4 w07 w06 w02 decimation06 (DecimationTrace.cons 3 w06 w05 w02 decimation05 (DecimationTrace.cons 2 w05 w04 w02 decimation04 (DecimationTrace.cons 1 w04 w03 w02 decimation03 (DecimationTrace.cons 0 w03 w02 w02 decimation02 (DecimationTrace.refl w02))))))))))))))))
  · exact (DecimationTrace.cons 13 w17 w16 w03 decimation16 (DecimationTrace.cons 12 w16 w15 w03 decimation15 (DecimationTrace.cons 11 w15 w14 w03 decimation14 (DecimationTrace.cons 10 w14 w13 w03 decimation13 (DecimationTrace.cons 9 w13 w12 w03 decimation12 (DecimationTrace.cons 8 w12 w11 w03 decimation11 (DecimationTrace.cons 7 w11 w10 w03 decimation10 (DecimationTrace.cons 6 w10 w09 w03 decimation09 (DecimationTrace.cons 5 w09 w08 w03 decimation08 (DecimationTrace.cons 4 w08 w07 w03 decimation07 (DecimationTrace.cons 3 w07 w06 w03 decimation06 (DecimationTrace.cons 2 w06 w05 w03 decimation05 (DecimationTrace.cons 1 w05 w04 w03 decimation04 (DecimationTrace.cons 0 w04 w03 w03 decimation03 (DecimationTrace.refl w03)))))))))))))))
  · exact (DecimationTrace.cons 12 w17 w16 w04 decimation16 (DecimationTrace.cons 11 w16 w15 w04 decimation15 (DecimationTrace.cons 10 w15 w14 w04 decimation14 (DecimationTrace.cons 9 w14 w13 w04 decimation13 (DecimationTrace.cons 8 w13 w12 w04 decimation12 (DecimationTrace.cons 7 w12 w11 w04 decimation11 (DecimationTrace.cons 6 w11 w10 w04 decimation10 (DecimationTrace.cons 5 w10 w09 w04 decimation09 (DecimationTrace.cons 4 w09 w08 w04 decimation08 (DecimationTrace.cons 3 w08 w07 w04 decimation07 (DecimationTrace.cons 2 w07 w06 w04 decimation06 (DecimationTrace.cons 1 w06 w05 w04 decimation05 (DecimationTrace.cons 0 w05 w04 w04 decimation04 (DecimationTrace.refl w04))))))))))))))
  · exact (DecimationTrace.cons 11 w17 w16 w05 decimation16 (DecimationTrace.cons 10 w16 w15 w05 decimation15 (DecimationTrace.cons 9 w15 w14 w05 decimation14 (DecimationTrace.cons 8 w14 w13 w05 decimation13 (DecimationTrace.cons 7 w13 w12 w05 decimation12 (DecimationTrace.cons 6 w12 w11 w05 decimation11 (DecimationTrace.cons 5 w11 w10 w05 decimation10 (DecimationTrace.cons 4 w10 w09 w05 decimation09 (DecimationTrace.cons 3 w09 w08 w05 decimation08 (DecimationTrace.cons 2 w08 w07 w05 decimation07 (DecimationTrace.cons 1 w07 w06 w05 decimation06 (DecimationTrace.cons 0 w06 w05 w05 decimation05 (DecimationTrace.refl w05)))))))))))))
  · exact (DecimationTrace.cons 10 w17 w16 w06 decimation16 (DecimationTrace.cons 9 w16 w15 w06 decimation15 (DecimationTrace.cons 8 w15 w14 w06 decimation14 (DecimationTrace.cons 7 w14 w13 w06 decimation13 (DecimationTrace.cons 6 w13 w12 w06 decimation12 (DecimationTrace.cons 5 w12 w11 w06 decimation11 (DecimationTrace.cons 4 w11 w10 w06 decimation10 (DecimationTrace.cons 3 w10 w09 w06 decimation09 (DecimationTrace.cons 2 w09 w08 w06 decimation08 (DecimationTrace.cons 1 w08 w07 w06 decimation07 (DecimationTrace.cons 0 w07 w06 w06 decimation06 (DecimationTrace.refl w06))))))))))))
  · exact (DecimationTrace.cons 9 w17 w16 w07 decimation16 (DecimationTrace.cons 8 w16 w15 w07 decimation15 (DecimationTrace.cons 7 w15 w14 w07 decimation14 (DecimationTrace.cons 6 w14 w13 w07 decimation13 (DecimationTrace.cons 5 w13 w12 w07 decimation12 (DecimationTrace.cons 4 w12 w11 w07 decimation11 (DecimationTrace.cons 3 w11 w10 w07 decimation10 (DecimationTrace.cons 2 w10 w09 w07 decimation09 (DecimationTrace.cons 1 w09 w08 w07 decimation08 (DecimationTrace.cons 0 w08 w07 w07 decimation07 (DecimationTrace.refl w07)))))))))))
  · exact (DecimationTrace.cons 8 w17 w16 w08 decimation16 (DecimationTrace.cons 7 w16 w15 w08 decimation15 (DecimationTrace.cons 6 w15 w14 w08 decimation14 (DecimationTrace.cons 5 w14 w13 w08 decimation13 (DecimationTrace.cons 4 w13 w12 w08 decimation12 (DecimationTrace.cons 3 w12 w11 w08 decimation11 (DecimationTrace.cons 2 w11 w10 w08 decimation10 (DecimationTrace.cons 1 w10 w09 w08 decimation09 (DecimationTrace.cons 0 w09 w08 w08 decimation08 (DecimationTrace.refl w08))))))))))
  · exact (DecimationTrace.cons 7 w17 w16 w09 decimation16 (DecimationTrace.cons 6 w16 w15 w09 decimation15 (DecimationTrace.cons 5 w15 w14 w09 decimation14 (DecimationTrace.cons 4 w14 w13 w09 decimation13 (DecimationTrace.cons 3 w13 w12 w09 decimation12 (DecimationTrace.cons 2 w12 w11 w09 decimation11 (DecimationTrace.cons 1 w11 w10 w09 decimation10 (DecimationTrace.cons 0 w10 w09 w09 decimation09 (DecimationTrace.refl w09)))))))))
  · exact (DecimationTrace.cons 6 w17 w16 w10 decimation16 (DecimationTrace.cons 5 w16 w15 w10 decimation15 (DecimationTrace.cons 4 w15 w14 w10 decimation14 (DecimationTrace.cons 3 w14 w13 w10 decimation13 (DecimationTrace.cons 2 w13 w12 w10 decimation12 (DecimationTrace.cons 1 w12 w11 w10 decimation11 (DecimationTrace.cons 0 w11 w10 w10 decimation10 (DecimationTrace.refl w10))))))))
  · exact (DecimationTrace.cons 5 w17 w16 w11 decimation16 (DecimationTrace.cons 4 w16 w15 w11 decimation15 (DecimationTrace.cons 3 w15 w14 w11 decimation14 (DecimationTrace.cons 2 w14 w13 w11 decimation13 (DecimationTrace.cons 1 w13 w12 w11 decimation12 (DecimationTrace.cons 0 w12 w11 w11 decimation11 (DecimationTrace.refl w11)))))))
  · exact (DecimationTrace.cons 4 w17 w16 w12 decimation16 (DecimationTrace.cons 3 w16 w15 w12 decimation15 (DecimationTrace.cons 2 w15 w14 w12 decimation14 (DecimationTrace.cons 1 w14 w13 w12 decimation13 (DecimationTrace.cons 0 w13 w12 w12 decimation12 (DecimationTrace.refl w12))))))
  · exact (DecimationTrace.cons 3 w17 w16 w13 decimation16 (DecimationTrace.cons 2 w16 w15 w13 decimation15 (DecimationTrace.cons 1 w15 w14 w13 decimation14 (DecimationTrace.cons 0 w14 w13 w13 decimation13 (DecimationTrace.refl w13)))))
  · exact (DecimationTrace.cons 2 w17 w16 w14 decimation16 (DecimationTrace.cons 1 w16 w15 w14 decimation15 (DecimationTrace.cons 0 w15 w14 w14 decimation14 (DecimationTrace.refl w14))))
  · exact (DecimationTrace.cons 1 w17 w16 w15 decimation16 (DecimationTrace.cons 0 w16 w15 w15 decimation15 (DecimationTrace.refl w15)))
  · exact (DecimationTrace.cons 0 w17 w16 w16 decimation16 (DecimationTrace.refl w16))
  · exact (DecimationTrace.refl w17)

/-- Actual kernel-checked FFT samples of the original locked 400-node input.
This is a kernel-only numerical theorem until the C execution refiner consumes
this same trace; it must not by itself be called source-first PV. -/
theorem sample_error
    (hmass : coefficientMass 131072 (fun j => decode (input 131072 j))≤81)
    (k : Nat) (hk : k<131072) :
    ‖decode (output.getD k (0,0))-
      dftSum 131072 k (negativeRoot 131072) (fun j => decode (input 131072 j))‖≤
        (1/50000000000000000:ℝ) := by
  apply complete_execution.error17 seed w17.tail
  · rw [←top_table_shape]
    exact top_table_length
  · exact seed_exact
  · exact global_twiddle_trace
  · intro t ht
    rw [←top_table_shape]
    exact all_stage_chains t ht
  · exact hmass
  · exact hk

#print axioms sample_error
#print axioms numerator_checked
end FapForest17
