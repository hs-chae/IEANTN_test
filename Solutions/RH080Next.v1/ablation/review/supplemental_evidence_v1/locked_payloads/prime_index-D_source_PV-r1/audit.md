# Reproduction and scope

Run /bin/lean /work/submission/Transport.lean (assigned wrapper); exit 0.
Printed axioms for the transport, profile and combined/refined consumers:
propext, Classical.choice, Quot.sound only. This is checking with the
frozen imports, not rebuilding the entire dependency graph.

- Generic order/count locators: Mathlib/Data/Nat/Nth.lean,
  Nat.nth_strictMono and Nat.count_le_iff_le_nth;
  Mathlib/NumberTheory/PrimeCounting.lean, Nat.add_two_le_nth_prime.
- CMS1708.04122v2.pdf, Theorem 3 (1.13), definitions (1.3), (1.12);
  IEANTN/Vocabulary/CMSFunctional.lean, SourceCMSPopulation;
  Scaled40ActualConsumers.lean, actual_population_curve. Kernel-only
  Gaussian chain. No C-source verification claim for it.
- Blanquer_Robles_2026.pdf, Lemma 5 §2.1 and Proposition 6 §3,
  eq:pair and eq:uniform-count; BRFourierInput/v1/Conclusions.lean
  contains exact predicates including full mesh and attained maximum.
  ExplicitBRPopulationConsumer.lean:53 discharges the vanishing
  remainder and handles padding. The q=1 specialization remains a
  named analytic input; neither RH alone nor executable output proves it.
- Assigned source-first BR chain: PopulationSource.lean and
  FlatPopulationSource.lean, actual_source_syntax; respective
  PopulationActual and FlatPopulationActual actual_norm_program,
  Main.actual_main_output, SourceFinal.actual_source_output and
  source_first_periodic_norm; AffineProgramsSolution.lean:29,40,
  PopulationActualConsumers.lean:14–33. Our source consumers compose
  these via the kernel-checked index bridge. The separate br theorem
  uses the matched kernel-only roots in RH080EstimatePack.
- Same fixed C bytes: population_norm.c SHA256
  92c5832d3ecfdd08d7c4143ac155e47e61ee9f58700634cf4f04e7cf8fc84b09;
  flat_population_norm.c SHA256
  2556f5eddca7d218a5e6565b4defed53aab957063ffbfadf5104f511a5fc82d9.
  Scope is the supplied fixed-input scalar checked C subset,
  AST/interpreter, and modeled decimal printing (ScalarHost.lean).
  Not arbitrary C/C++/CUDA, external compiler correctness, libc,
  OS, hardware or the original incomplete large FFT migration.

Negative work: the first margin proof used delta*sqrt(x)>4, which
did not cover the three units budgeted in its intermediate inequality;
replaced by >8. Continuum parameter intersection is not justified;
finite grids replace it. No exact unslacked Gaussian rank bound
or explicit onset was obtained. PNT normalization and limsup
interpretation are written derivations, not additional checked Lean
theorems.
