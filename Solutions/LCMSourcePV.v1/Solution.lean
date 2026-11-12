/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import WitnessLcmNodeConsumer

/-- The original existing Lcm.v1 challenge, using the source-first proof.
This supplementary solution has no official Comparator/NanoDa receipt. -/
theorem Lcm.v1.challenge_lcmUpto_not_highlyAbundant
    (dusart2018_v1_proposition_5_4 : Dusart2018.v1.proposition_5_4) :
    Lcm.v1.lcmUpto_not_highlyAbundant :=
  LCMSourcePV.Network.lcm_v1_source_first dusart2018_v1_proposition_5_4

#print axioms Lcm.v1.challenge_lcmUpto_not_highlyAbundant
