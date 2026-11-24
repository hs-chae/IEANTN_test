/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import OcticExplicitFormula
import NetworkConsumers
import IEANTN.Nodes.GreenSmooth.v1.Conclusions
import IEANTN.Nodes.PrimeKernelInputs.v3.Conclusions
import IEANTN.Nodes.PrimeInterval.v3.Conclusions
import IEANTN.Nodes.PrimeQuantile.v2.Conclusions
import IEANTN.Nodes.Nicolas.v1.Conclusions
import IEANTN.Nodes.PrimeKernelInputs.v2.Conclusions
namespace PrimeKernelInputs.v3
open Real Set
theorem challenge_octic_family_explicit_formula (hg : GreenSmooth.v1.formula)
    (hn : Nicolas.v1.spectral_bound) : octic_family_explicit_formula :=
  fun _ hC => RHOcticPush.ExplicitFormula.explicit_formula_from_general_sources hg hn hC
theorem challenge_octic_215_explicit_formula (hg : GreenSmooth.v1.formula)
    (hn : Nicolas.v1.spectral_bound) : octic_215_explicit_formula :=
  challenge_octic_family_explicit_formula hg hn (43/20) (by norm_num)
end PrimeKernelInputs.v3
namespace PrimeInterval.v3
theorem challenge_count_215 (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_215_explicit_formula)
    (hz : PrimeKernelInputs.v2.octic_215_zero_estimate) : count_215 :=
  RHLimit.OcticTwoInputs.prime_count_215 rh he hz
theorem challenge_count_family (rh : RH.v1.hypothesis)
    (he : PrimeKernelInputs.v3.octic_family_explicit_formula)
    (hz : PrimeKernelInputs.v2.octic_family_zero_estimate) : count_family :=
  RHLimit.OcticTwoInputs.prime_count_family rh he hz
end PrimeInterval.v3
namespace PrimeQuantile.v2
theorem challenge_octic_block (hi : PrimeInterval.v3.count_215) : octic_block :=
  RHContinuation.Network.octic_block hi
theorem challenge_successive_cubes (hi : PrimeInterval.v3.count_215) : successive_cubes :=
  RHContinuation.Network.successive_cubes hi
end PrimeQuantile.v2
namespace RHOcticPush.Network
/-- Entire derived-EF propagation; original sharp zero estimate still explicit. -/
theorem octic_network (hg : GreenSmooth.v1.formula) (hn : Nicolas.v1.spectral_bound)
    (rh : RH.v1.hypothesis) (hz : PrimeKernelInputs.v2.octic_215_zero_estimate)
    (hzf : PrimeKernelInputs.v2.octic_family_zero_estimate) :
    PrimeKernelInputs.v3.octic_family_explicit_formula ∧ PrimeInterval.v3.count_215 ∧
    PrimeInterval.v3.count_family ∧ PrimeQuantile.v2.octic_block ∧
    PrimeQuantile.v2.successive_cubes := by
  have ef := PrimeKernelInputs.v3.challenge_octic_family_explicit_formula hg hn
  have fixed := PrimeInterval.v3.challenge_count_215 rh
    (PrimeKernelInputs.v3.challenge_octic_215_explicit_formula hg hn) hz
  exact ⟨ef,fixed,PrimeInterval.v3.challenge_count_family rh ef hzf,
    PrimeQuantile.v2.challenge_octic_block fixed,PrimeQuantile.v2.challenge_successive_cubes fixed⟩
end RHOcticPush.Network
#print axioms PrimeKernelInputs.v3.challenge_octic_family_explicit_formula
#print axioms PrimeInterval.v3.challenge_count_215
#print axioms PrimeQuantile.v2.challenge_octic_block
#print axioms RHOcticPush.Network.octic_network
