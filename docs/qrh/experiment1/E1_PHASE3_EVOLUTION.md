# Experiment 1: evolved programs

Status: actual proof closure and all E method-control matrices complete. The immutable E checkpoint records the sealed artifacts; this is not the final N+ decision.

## Outcomes and fair comparison

All statements are conditional on the exact common input strata in E1_PREMISES_AND_ROUTES.csv. P0 keeps the original CH2 package, PrimaryInputs8 at (0.3681,0.3599), finite RH only through 3e12, RVM/small-zero inputs, and QRH on the open half-plane Re(s)>7/8, excluding the pole. P1 additionally grants the CHJ-II common-height increment theorem to BOTH arms; the old FKS uniform-density contract is retained when the raw/factored route uses it. No computation receives credit for a stronger source premise.

The actual evolved psi and direct weighted-sum coefficient is 1826923053/200000000000 = 0.009134615265, valid for EVERY REAL x >= exp(330). The two quantities are Epsi=|psi(x)-x|/x and |sum_{n<=x} Lambda(n)/n - log(x) + EulerGamma|. They are different quantities with two actual consumer proofs. The pi coefficient is 9134616/1e9 = 0.009134616, also on that full real ray, with Epi=|pi(x)-Li_2(x)|/(x/log(x)), using the repository's offset Li_2 normalization. This uses the strongest MixedProof theorem, not the older 0.0091347 rounding.

E1Evolved.pairBound is min(E1FrozenN.finalErrorBound, kappa_E*x^(-1/8)). E1Evolved.piBound preserves the ENTIRE old PVEvolutionA.bestBound above exp(300), and adds the new pi ray by a minimum only where x>=exp(330). Thus old pointwise/piecewise routes remain available far out. E1Evolved.evolved_pair and evolved_pi are the actual cumulative consumers.

On the CLOSED domain exp(330)<=x<=exp(331), E1Evolved.pair_full_closed_domain_strict and pi_full_closed_domain_strict prove a strict allowance margin larger than 2e-6*x^(-1/8) against the FULL completed N functions, including their pointwise and piecewise minima. A source-linked lower enclosure proves the old allowance function is at least 0.0091369*x^(-1/8) there. This is a lower bound on an allowance, never a lower bound on the actual prime error. No global strictness or mathematical optimality is inferred.

## Genuine new high-anchor evolution

HighAnchorIntervalB.v1 is new in this experiment, beyond historical reference091288df. For every REAL x>=exp(330), it proves a prime in (x, x+0.88*x^0.79]. Parent HighAnchorIntervalA used 0.92*x^0.79. New B changes c to22/25, k to201/88, T to(3000/11)*L*exp(0.21L), and h*T to240*L*exp(L). It retains 256 sigma cells and the same source package. The verified profile is at anchor3e12*exp(40), K=6.90401 and slope5.56817. It does NOT assert RH up to that anchor: finite RH remains3e12, and the density theorem controls higher zeros.

The whole-real bridge proves: psi increment error <=(1989/2000)*h; theta increment >=(9/2000)*h. All outer integrals, height applicability, clipping, finite-zero sums, prime powers, antitonicity and exp/log conversion are discharged in the real proof. The endpoint is not a sample at L=330. The numeric high budget is0.94, low budget0.03, explicit-formula truncation0.0245, prime-power allowance0.001.

All18 B modules passed fresh canonical compilation. New ProfileProgram11.64s, MomentRuns17.50s, LowProgram3.47s. Compatible actual-QRH compilation separately reevaluated B's numerical facts under Lean4.34.1; all18 modules and three genuine wrappers passed. E1HighAnchorActual supplies OpenAI's actual theorem and has14 native facts per root; OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re itself has only propext, Classical.choice, Quot.sound. The body audit checks actual OAI reachability, every root argument used, and all8 PrimaryInputs projections consumed. The four remaining B premise packages are CHJ-II, PrimaryInputs8, finite RH3e12 and RVM. This is conditional validity, not a full formalization of those literature packages.

E1Evolved.frozen_prime_width_strict proves the new width is strictly smaller than N's0.01839254524623*x^(7/8) on the whole common ray. B's union theorem separately compares with x^(4/5) under the honest enlarged union including FKS. These are pre-N+ comparisons, not the final experiment verdict.

## Real output-to-input dataflow

In B, momentOutput(i)=runRow(momentRow(i)); momentCap(i)=momentOutput(i).interval.hi.toRat; weightedExpr(i)=weightExpr(i)*literal(momentCap(i)). All256 computed upper endpoints enter the next budget program as actual outputs. Its source/model equality and generic soundness theorem turn the result into an integral bound used by the prime theorem. The mutation matrix changes the actual A output selection from hi to lo.

The calibration stage's K/slope flow uses certified literal advertised caps, rather than raw returned endpoints. That edge is certified-bound transport. It is not claimed as raw A-output composition. The moment-to-budget edge is the genuine output composition. There are6 instances of ONE lean-dyadic-expr backend, not6 independent numerical algorithms.

## Other evolved families

C compares new raw512 and factored64 programs, both outside F at this historical start. Their increment allowances are0.408514*h and0.405513*h for h=x^0.8, all real x>=exp(330), under identical CHJ-II/FKS/RVM/QRH inputs. The factorization reduces cells and the executed bound. Both already prove prime existence; that Boolean conclusion does not improve. The exact N analytic profile remains in the baseline, so rounded cap comparisons alone are not a strict full N-function win. Fresh factored EvolvedRuns completed25.56s. Historical source-linked C512/C64 controls45/50 are reused by exact current source/object hashes, not called newly executed.

D recalibrates from4 old profiles/4 old Gaussian kernels to128 profiles and18 Gaussian kernels, using8192 strip cells in8 chunks with mixed precision. Chunks4,5,6 use precision-80/Taylor20; others use the old Fast precision-80/Taylor16. New direct weighted and psi consumers use the actual capped mixed outputs. Heavy native certificates retain exact source/object-associated historical evidence. Current PsiCompanion, strongest MixedProof, cumulative consumers and actual-QRH wrappers passed fresh elaboration. The old D mutation matrices60 native-route controls plus15 pure-cotangent controls are reused unchanged, not reported as fresh. The pure cotangent proof removes hcs from the13-input CH2 package; this is an analytic gain available to N+ too. The generic9*kappa to direct1*kappa gain was already admitted in N, so is not attributed to E.

## Verification and evidence limits

Canonical: Lean4.34.0-rc2 / Mathlib71a80585ee495fc24472fd0eaffc89d94e4fd8d6. Actual QRH: Lean4.34.1 / Mathlibd13f23b723b8a846827a245b89c10fc7d3f11612. No cross-pin objects. Public QRH source openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, written Theorem1.1 PDFp4. Conditional source declarations remain visible in actual root types. Native evaluation trusts the pinned Lean compiler/runtime and host behavior; the result is native-assisted research evidence, not official Std3 Comparator acceptance or a kernel-only proof.

Actual root audit is evidence/E/PROOF_AUDIT.json. All nonstandard leaves are mapped by written (file,declaration,line), never collapsed by bare names. Historical exact-source gate reuse is evidence/E/HISTORICAL_GATE_SOURCE_REUSE.json. New B checks use the unchanged checker, extractor and semantics from the reference; only a PRIVATE recipe/fixture was added, outside the mathematical repository. The190 fresh B controls passed in five Python optimization modes. The comparison floor has a separate existing two-route gate with50 fresh controls passed before sealing. Original floor source differs only by a leading copyright comment in nine modules, proven by exact hashes after removing that comment. The private gate uses current headed source and matching header-replayed objects; its recipe hashes are local to the fixture. A duplicate4096-box native run timed out after300.364s; its old verified certificate is reused, and no fresh successful large certificate is claimed. Three ordinary current floor modules passed fresh replay. No acceptance assertions, schema changes or official receipt edits are used.

The first B LowRay retained the old logarithm coefficient6000/23 and failed Lean; corrected to6000/11 and replayed the full consumer closure. Failed stages and all partial control runs remain in evidence/RESEARCH_FAILURES.md and stage logs. This is not a cold library replay or a new speed benchmark.

## Attribution and remaining work

See E1_REVERT_TESTS.md and E1_PROGRAM_LINEAGE.csv. Reverting to old numeric outputs recovers the old valid direct consumer; analytic factor9 removal survives. Reverting B's truncation budget makes the selected bound exceed1; reverting the parent's k fails the clipping contract for width0.88. Neither proves universal computational necessity. Strong analytic competitors remain serious.

The starting registered census remains114 versions/58 families/240 conclusions plus3 explicit empty-source stubs. The frozen2080 tracked files, core, schema, official nodes, protected statements and fingerprints remain unchanged. New mathematical material is isolated in Solutions; no official new node/dispatch, push or PR. This research does not claim a full primary-source audit of the network. Existing Ramanujan exp145 and other better old conclusions remain in their cumulative families; no new Ramanujan cutoff or tertiary winner is claimed.

An unproved E-stage analytic design note suggests changing clipping/height and analytically bounding the high integral with the OLD profile, perhaps reaching0.86*x^0.79. It is only an unadmitted threat at this checkpoint, with no new numerical fact. N+ must independently complete or reject it.

After the immutable E checkpoint, the SAME agent must execute at least two substantive N+ attacks using only F plus new analytic reasoning. No E numerical profile, Gaussian array, certificate or equivalent recomputation becomes F. The final strict winner question remains open until then.
