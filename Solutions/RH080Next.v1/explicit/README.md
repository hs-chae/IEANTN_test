# Explicit affine Fourier and prime-bound continuation

These files prove reusable analytic sublemmas for the **unchanged** written
0.851062 global and 0.8 finite-range constructions. They do **not** yet prove
either final prime bound. Original RH080Study.v1 sources/results are untouched.
There are no `sorry`, added axioms, native numerical execution leaves, or
unverified numerical-output premises in these mathematical modules. Literal numerical bounds in source-provider consumers are supplied by their actual source-linked proofs.

## Proved in Lean

- `ExplicitAffineWindow`: the actual even affine spectrum W, as a sum of hats,
  is continuous, supported in its stated radius and integrable.
- `ExplicitHatIntegrals`, `ExplicitAffineIntegrals`, `ExplicitNodalMoments`:
  actual integrals equal the finite nodal mass formula; the absolute mass and
  second moment are bounded by the precise finite coefficient formulas. In
  particular ∫ v²|W(v)| ≤ `nodalMu2Upper`.
- `ExplicitHatFourier`, `ExplicitAffineFourier`, `ExplicitFiniteDifference`:
  actual triangle transform by piecewise integration; F(u) = sinc²(πu/m)P(u/m)/m;
  discrete second differences, including both outer slope jumps, prove
  |F(u)| ≤ V₁/(4π²u²) for every nonzero u.
- `ExplicitFourierPair`, `ExplicitCMSEligible`: actual complex Fourier equality
  Fourier(F) = W, actual integrability of F, and membership in the existing
  CMS function class. These conclusions are not assumed from a certificate.
- `ExplicitSignedLogMoment`, `ExplicitCosineMoment`,
  `ExplicitAffineSignedMoment`: the signed logarithmic moment really means
  ∫ |F(u)| log|u|; its integral exists. The central quadratic lower bound and
  the sharp variation tail yield, at τ = 3/8, the written upper formula
  V₁/(2π²) − 2F(0)τ(1−logτ) + 40μ₂τ³(1/9−logτ/3).
- `ExplicitDomain`, `ExplicitWindowErrors`: the full continuous domain t ≥ 42,
  1/2 ≤ c ≤ 1 gives 0 < d < 2×10⁻⁸, the lower support endpoint exceeds x/2,
  and the pole scale lies between ct/2−10⁻⁶ and ct/2. Also
  log(1/d) ≤ t/2−log(ct/2)+10⁻⁶. Support-seven mollification by radius at most
  one stays inside a fixed positive compact interval, with one fixed finite
  integer envelope.
- `ExplicitMellinFourier`: the actual Mellin kernel has Fourier transform
  2π W((2πξ−L)/d), by a proved change of variables and phase normalization.

- `ExplicitEntireUniqueness`, `ExplicitCompactLaplace`, `ExplicitMellinPoles`:
  the entire extension equals the actual compact Fourier–Laplace integral;
  both imaginary endpoint values are evaluated from that same function.
- `ExplicitDigammaDifference`, `ExplicitDigammaFubini`, `ExplicitGammaFourier`,
  `ExplicitGammaAffine`, `ExplicitGammaSubstitution`,
  `ExplicitSecondPoleIntegral`, `ExplicitMellinGammaCancellation`: DLMF's general
  digamma integral is subtracted at real part 1/4; nonnegativity gives the
  absolute double-integral bound needed for Fubini. The actual Gamma term is
  transformed to positive Mellin coordinates and cancels the second pole,
  leaving exactly the actual trivial-zero integral. No additional Stirling
  or window-specific Gamma assumption is used.
- `ExplicitMellinIdentity`, `ExplicitRHMellin`: the complete actual affine
  Mellin identity, with the actual von Mangoldt sum, actual zeta zeros and
  multiplicities, actual real zero ordinates under RH, pole and trivial term.
  The wider-support application is derived through the previous analytic
  theorems, not supplied as a source-seven premise.
- `ExplicitPoleError`: the actual pole integral differs from F(0) by at most
  b²μ₂ when |b|R ≤ 1; the signed linear term vanishes by evenness.
- `ExplicitBRPopulationConsumer`: the literal general BR population source
  proposition at modulus one is connected to the existing actual prime-count
  predicate. Its remainder tends to zero in Lean. The source and matched
  kernel-only wrappers in `ExplicitPopulation*` and `ExplicitFlatPopulation*`
  consume the separate actual m8 numerical programs and establish eventual
  width 2.108 for population parameter one, and the complete flat family
  9/8 + (16/15)α for every α ≥ 0. These have no explicit onset. The same
  mathematical conclusions hold in the matched kernel-only control; PV adds
  source provenance, not a quantitative gain relative to that control.

## Locked inputs and algorithms

`LOCKED_PROFILE_PROVENANCE.json` preserves the exact original claim/input and
algorithm associations and distinguishes independent posthoc evaluation.

| Claim | Frozen profile | Mesh / scale / raw coefficients | Original norm grid / blocks k | Independent global-chord grid / k |
|---|---|---|---|---|
| 0.74 through exp(63), from x = 11 | Fap | 80 / 10¹² / 400 | 1,048,576 / 12 | 524,288 / 16 |
| 0.75 through exp(70), from x = 11 | Fap | 80 / 10¹² / 400 | 1,048,576 / 12 | 524,288 / 16 |
| 0.8 through exp(174), from x = 4 | Fap | 80 / 10¹² / 400 | 32,768 / 16 | 131,072 / 16 |
| 0.851062 on x ≥ 4 | w4 | 360 / 10¹⁶ / 2,520 | 524,288 / 1 | 16,777,216 / 1 |
| 0.851061745 + 1.505657839α, eventual | w4 | same w4 | posthoc reuse of the independently evaluated 16,777,216-point norm; no finite-x block parameter | same |

Both profiles append one zero mathematical node. Fap has support radius five;
w4 has radius seven. Fap SHA256 is
`9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a`;
w4 SHA256 is
`61f745f27018ea5addbb01c1d583b128b2639b0f101d764136c98c26983c5521`.
The original 0.74/0.75 derivation uses τ = 0.45 and right-closed endpoints;
the independent posthoc route uses τ = 3/8 and a separately proved strict
endpoint upgrade. The strongest original 0.8 and w4 ray routes use τ = 3/8.
No w4 slab is substituted for any Fap result.

## Precisely identified literature inputs

These are ordinary proposition parameters, **not Lean axioms**. Their source
proofs remain literature-backed. An axiom audit reporting the three standard
Lean axioms does not discharge these proposition parameters.

| Actual declaration | Primary source statement | Application and boundary |
|---|---|---|
| `SourceBRFourierNormStrip` in `ExplicitBRStripTransfer` | BR v2, subsection “The Fourier pair and its norm”, Lemma `lem:fourier-norm`: arbitrary rational nodes with N = 5m, outer nodes zero; the inverse transform extends to an entire function and F and F′ decay quadratically on **every fixed horizontal strip**. | `affine_strip_extension_by_mesh_dilation` proves the actual wider-support application. For w4, N = 2520 = 5×504; changing mesh 504 to 360 scales the complex argument by 7/5, and widens the strip by the same factor. `mellin_test_function_strip` proves the full Mellin test function is entire with the required strip decay for every positive d. |
| `SourceBRFourierNormFive` in `ExplicitNormSourceBridge` | The **same general lemma**, equation `eq:pair`, states ∫ over the real line |F| = ∫ from 0 to 1 |P|. | Actual L1 mesh invariance and exact zero-padding are proved in Lean. The input applies to w4 through mesh 504, and to the new m8/support2 profile through zero-padding to 41 nodes. The underlying sinc² periodization identity has **not** been re-proved here; this boundary remains explicit. |
| `SourceCMSGuinandWeil` in `ExplicitGuinandWeilApplication` | CMS arXiv:1708.04122v2, Lemma 6, printed p.17/PDF p.17, citing Iwaniec–Kowalski Theorem 5.12: the general Guinand–Weil formula for an analytic strip of width greater than 1/2 and decay exponent greater than one. | Our input restricts this general source theorem to entire functions with quadratic strip decay. It uses actual zeta zeroes/multiplicities, actual von Mangoldt values, the actual Fourier transform and digamma function; convergence is explicit. `guinand_weil_affine_test` derives its actual affine-kernel application from the general source contracts. |

Additional named inputs are `SourceDLMFDigammaIntegral` (official DLMF
5.9.16, domain Re(z) > 0; source section 5.9 confirms this domain) and
`SourceBRUniformPopulationQ1` (BR v2, Proposition `prop:uniform`, equation
`eq:uniform-count`, with F as in the general Lemma 5 and D₄ > 0; restrict
modulus family to {1}). The former is consumed by the actual Gamma elimination;
the latter by actual eventual prime-population consumers. BR's section on
moduli one and two states that RH suffices for this specialization. These
remain explicit literature propositions, not kernel reproved source theorems.

No standalone Blueprint label has been added for these new sublemmas. The
existing imported class correspondence is `IEANTN/Vocabulary/CMSFunctional.lean`;
root integration owns any node/Blueprint registration.

**Do not generalize BR equation (15) into a source input for arbitrary nodes.**
The printed explicit section first fixes F to its particular F_GRH witness.
Its proof is informative but does not license calling an arbitrary-window
Mellin identity the literal printed theorem. No `SourceBRMellinFive` assumption
has been introduced. The genuinely general CMS Lemma 6 is used instead.

## Remaining obligations for the old explicit bounds

1. Derive the precise zero-count/Stieltjes remainder, including the derivative
   variation constant and all endpoint/infinite-tail limits.
2. Prove the Montgomery–Vaughan outer-level-set count, prime-power contribution,
   and every term in the aggregate 0.0012 allowance.
3. The w4 scalar C source now has an actual source/AST/main execution proof
   and finite nodal outputs. `ExplicitW4SourceMoment` consumes those outputs
   in the actual signed-log integral theorem. Remaining w4 work includes
   actual exterior J/H refinements and its original FFT norm enclosure.
   Fap's distinct 400-node numerical provider and 131,072-point norm remain
   separate obligations for the locked finite frontier. The new small
   population programs do not complete either old profile.
4. Complete continuous residual/slab/ray and strict prime endpoint consumers,
   and integrate the separate small-x bridge.

The current work does not promote either old explicit bound into the verified
network. Source-first numerical PV is implemented in the sibling `pv/` lane;
ordinary kernel evaluation of these analytic proofs is not called PV.

## Reproduce from a clean proof bank

Use Lean 4.34.0-rc2 and mathlib commit
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6` with its pinned generic dependencies.
The compiler SHA256 used in development is
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The generic replay requires no application theorem bank; the source-provider consumer modules require the separately reproduced sibling pv/ and primal/ sources. A context JSON supplies the absolute
compiler executable and a colon-separated `generic_lean_path` containing only
mathlib and its pinned generic dependency object libraries.

```sh
python3 reproduce.py --context /path/to/pinned-context.json --out /path/to/new-output
```

The output path must not exist. The script compiles every selected generic mathematical source and
both imported IEANTN vocabulary files into a **fresh** bank, preserves the
exact sources, commands, hashes, stdout/stderr, time/peak-memory reports,
proof-dependency audits and an atomic developer `RESULT.json`. It never writes
an IEANTN Comparator acceptance receipt. Default per-process address-space cap
is 32 GiB for these small proofs; `--memory-gib` permits a justified larger run
up to the owner's separate 300 GiB allowance. The script uses explicit errors,
not Python assertions, for acceptance checks. No random seeds or generated
numerical datasets occur in this lane.
