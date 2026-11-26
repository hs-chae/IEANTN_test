# Explicit affine Fourier and prime-bound continuation

These files prove the complete analytic and scalar-source chains for the
**unchanged** original Fap 0.74/0.75/0.8 slabs, original w4 0.851062 global
construction and its all-alpha eventual weighted curve. The final `_of_norm`
theorems explicitly retain the two unfinished original-input FFT norm bounds
as arguments: these are not yet fully source-first verified prime bounds.
Original RH080Study.v1 sources/results are untouched. All compiled proof roots
have only the three standard Lean axioms; numerical arguments and named
literature propositions are reported separately from axiom audits.

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

## Quantitative analytic closure after the first checkpoint

`ExplicitCMSZeroSource` exposes the general CMS Section 6.1 summation-by-parts
proof scheme as a named literature proposition; it is not claimed to be a
kernel reconstruction of Stieltjes integration from Lemma 9 alone. Every
actual affine admissibility obligation is proved in
`ExplicitAffineZeroAdmissible`: C1 regularity, both sharp quadratic tails,
actual integrability, and both vanishing infinity boundary terms.
`ExplicitCMSZeroRoot` proves an exact root Q(T₀) = 0 with 9 < T₀ < 10 by
rational inequalities and IVT, so there is no numerical root oracle.

`ExplicitAffineZeroEstimate` and `ExplicitZeroAllowance` consume those proofs,
retain the actual negative signed-log moment, and prove the complete zero plus
cutoff allowance < 0.0001. After logarithmic-height linearization, the actual
Mellin spectral norm is bounded by
U[t/2 − log(ct/2)] + nodalSignedLogUpper(3/8) + 0.000102.
`ExplicitTrivialError` proves the actual logarithmic substitution, integral
bound and < 10⁻⁸ allowance; `ExplicitPoleQuantitative` supplies < 10⁻¹⁰.
The composed `ExplicitMellinLower.actual_mangoldt_lower` consequently proves
an actual von-Mangoldt-sum lower bound with derived error 0.00011 over the
full t ≥ 42, 1/2 ≤ c ≤ 1 domain. Its named general literature inputs remain
explicit. The separate actual prime-power sum is kernel bounded by 0.001 in
the primal lane, using `ExplicitPrimePowerAllowance`.

The root/primal lanes prove the finite atomic BV inequality, its continuous
limit, exact affine positive-cell integrals and both normalized-wing H
identities. `ExplicitMontgomeryVaughan` preserves actual floor prime counts
and exact half-open endpoints. `ExplicitMVAtomic` derives the actual atomic
interval bound from one enlarged MV interval, with its literal physical
length ell. No connected-component or quadrature oracle is assumed.
`ExplicitResidual` proves the continuous slab minimum, complete-ray
monotonicity, and the margin needed to remove an upper endpoint prime.

Fresh frozen-source generic replays passed in normal, -O and -OO modes:
83 modules,78 theorem-axiom audits,264.40–266.08 seconds per run, maximum
process RSS3,988,928KiB,zero OOM events,about36.14MB per run. The complete
actual arithmetic/final analytic consumer, profile scalar residuals and
arbitrary-c population transfer are included. The only import libraries are
the eight pinned generic dependencies; every selected application math source
is freshly compiled from its immutable snapshot. The actual original C
providers and fixed-profile consumer builds have separately associated
source/build receipts, with a final joined provider replay tracked by pv/.

## Completed final consumers and the remaining numerical leaves

`ExplicitPrimeWeights`, `ExplicitCentralPrimes`, `ExplicitMVConstants`,
`ExplicitErrorBudget` and `ExplicitAnalyticTransfer` consume the actual
prime-wing/arithmetic and prime-power proofs, retain the exact original
block ell=sqrt(a)/k, derive the unchanged B=4.00001 allowance, and prove the
strict endpoint prime consumer with derived total budget0.0012.
`ExplicitScalarLogBounds`, `ExplicitProfileScalars` and
`ExplicitProfileResiduals` prove the actual signed-log scalar caps and all
continuous residual inequalities, including the whole w4 ray.

`ExplicitProfileApplications` consumes the source-first C scalar/J/V0
providers of both distinct frozen profiles. `ExplicitFullRangeApplications`
joins the historical finite source bridge and direct small cases:

- `fap_074_full_of_norm`: all real11≤x≤exp63, coefficient0.74, strict endpoints.
- `fap_075_full_of_norm`: all real11≤x≤exp70, coefficient0.75, strict endpoints.
- `fap_08_full_of_norm`: all real4≤x≤exp174, coefficient0.8, strict endpoints.
- `w4_global_full_of_norm`: all realx≥4, coefficient0.851062, strict endpoints.

Each theorem retains its actual inverse-Fourier L1 norm bound explicitly.
The caps use recorded independent global-chord review computations on the
original frozen data: Fap0.7817960157900848 at G131072 and
w40.7813568381304104 at G16777216. They are distinct from the original timed
programs. The constant names `fapOriginalNormCap`/`w4OriginalNormCap` refer to
the original input profile, not the timed algorithm. No new unverified FFT
output has been accepted, and no original score/outcome changes.

The support-seven all-alpha derivation is now kernel-proved:
`ExplicitAsymptoticWidth`, `ExplicitAsymptoticAllowances` and
`ExplicitAsymptoticCentral` derive the actual central-sum asymptotics for any
fixed c>0, from the actual Mellin/zero/prime-power/MV paths.
`ExplicitActualPopulation.actual_population_goodCoefficient` connects this
to the actual IEANTN pi predicate. `ExplicitW4Population` consumes the actual
source maximum output and proves
`w4_recorded_population_of_norm`: every alpha≥0 has the recorded width
0.851061745+1.505657839alpha, conditional on the actual w4 norm. This uses no
support-five uniform-population premise and claims no explicit onset.
`ExplicitW4StrictPopulation` also exhibits a strictly smaller good coefficient
and proves the exact strict infimum comparison with the recorded line;
endpoint membership alone is not substituted for that conclusion.

The two large source-first FFT norm proofs remain open. Consequently these
original-profile claims are not promoted as fully verified network results.
See `REMAINING_B.md` for the precise compiled statements and remaining leaves.
Ordinary kernel evaluation of the analytic proofs is not called PV.

## Completed source-helper verification

`ExplicitFFTCompareBase/Loop/Determinism/Call/Source/Audit` verify the actual
`magnitude_compare` C helper in both preserved `pv/fft/w4_fft.c` and
`pv/fft/fap_fft.c`. It reads five base-billion words from highest to lowest,
returns2/0/1 for greater/less/equal mathematical integers, and writes neither
input. The proof includes actual parameter/local allocation, array reads,
uint64 subtraction and comparisons, every loop/early-return branch, return
conversion and scope restoration. It proves correctness of every permitted
full source Call, both unchanged typed input arrays and every pre-existing
caller object; same or overlapping input slices are allowed.

The independent source-syntax proof and positional-integer correctness are
actually consumed, and the final audit checks those proof edges. The real C
bytes exactly match the formal source strings. The compiler/LP64/ULL64 ABI,
chosen restricted C execution-model adequacy, core runtime, OS and hardware
remain explicit trust boundaries; caller array/digit preconditions must be
established by the larger application. The source-to-AST, execution and
correctness contract is complete; its final ANT connection is pending.
Under the owner's definition this standalone helper is not yet completed
source-first PV. It does not complete either FFT program's numerical norm
output or its ANT theorem.

The normal source-cold helper replay compiled49sources in949.43seconds,
peak Lean RSS38,804,720KiB(about37GiB),zeroOOMs,about421MB retained artifacts.
Thirty supplementary native cases per C file include equality, shared and
overlapping read-only inputs; the universal Lean proof does not rely on
these tests. The full optimized Python CLI replays also passed:996.78seconds
under `-O` and981.76seconds under `-OO`, each49fresh sources and zeroOOMs.

The subsequent actual `increment_words` and `divide_small` source contracts
also passed71-source cold replays in all three Python modes, including exact
integer increment/floor/ceiling, every permitted call argument order, word
guards and temporary lifetimes. Their final ANT connection remains pending;
see `INTEGER_HELPERS.md` and `INTEGER_HELPERS_MANIFEST.json`. Historical
receipt fields containing `helper_PV_complete` retain their original values
and denote only that helper-contract milestone.

`ExplicitApplicationBirthFrame` proves persistent typed locals survive a
distinct temporary declaration and provides actual declaration/store/block
frames with fresh local births. Its standalone20source cold replay passed
in57.30seconds,peak3,439,028KiB. The frame permits new/dead temporary objects
and monotone allocation counters; it assumes neither unchanged allocation
counters nor that all later objects existed before. It is used by actual
source multiplication/addition/division proofs, not an expansion of trusted
runtime behavior. Incomplete increment/division source proofs are excluded
from the accepted publication manifest.

The final six original-profile conditional consumers, including the strict
coefficient-infimum conclusion, were freshly compiled and dependency-audited
against exact source/hash/receipt-associated corrected C scalar providers.
The final overlay took16.48seconds,peak4,489,880KiB. This overlay is labelled
source-associated; the83generic math sources, original scalar providers and
finite bridge have their own actual source-cold receipts. No FFT norm premise
is hidden or promoted into a verified network result.

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

For the source-helper reproduction (actual C compilation/tests plus every
local source proof freshly compiled), run from any directory:

```sh
python3 reproduce_fft_compare.py --context /path/to/pinned-context.json --out /path/to/new-helper-output
```

To rebuild the complete original-profile conditional theorem closure directly
from clean sources, reuse the sibling source-cold compiler:

```sh
python3 ../pv/reproduce_lean.py --context /path/to/pinned-context.json --run /path/to/new-full-proof-output --root ExplicitOriginalFinalAudit
```

That larger clean replay regenerates the scalar proof closures as well and
can take over an hour and tens of GiB. The faster final development overlay
reuses only exact receipt-associated objects from the independently completed
source-cold phases; it is never labelled a new source-cold replay.
`export_proof_bank.py` only adapts a completed generic replay's receipt format
after checking original source/object/log/resource/compiler hashes; it does
not run a new proof or issue a new acceptance.
