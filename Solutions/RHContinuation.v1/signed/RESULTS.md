# Signed continuation: accepted mathematics and source boundaries

This is new post-lock continuation work. Historical submissions and the previous `.006` proof remain untouched. Mathematical roots are in `source/`; full run logs are in `/data/ivy-rh-continuation-20261122/signed/`. These are ordinary kernel proofs conditional on stated source predicates. They are not source-first PV, Comparator receipts or a proof of RH.

## A stronger first-Mertens lower margin from recovered cube tails

Use the unchanged actual definitions `MertensPositive.A`, `CA`, `q`, `E` and `fullTail`. Thus A sums log(p)/p over actual primes p≤x and E=−γ−sum over all primes log(p)/(p(p−1)). The exact algebraic identity is A−logx−E=(CA−logx+γ)+fullTail.

`first_mertens_positive_cube_IEANTN` proves, for every real x in the complete closed band exp(24)≤x≤10^19,

    A(x)−log(x)−E > .014/sqrt(x).

The predecessor is the previous post-lock theorem `.006/sqrt(x)` on exactly the same band. The new uniform constant is 7/3 times the old one. The actual remaining inputs are exactly the same: RH; BFKNW Proposition29(ii), Eq(154); BFKNW Lemma21's convergent reciprocal-ordinate mass cap `.04620999`; and the existing three Büthe Theorem2 conclusions for ψ and signed θ. No new prime list, zero table, empirical sign, target-as-premise, execution axiom or numerical source predicate is introduced.

The old finite correction bound assigned the complete geometric correction q(p) to every prime p≤sqrt(x). If x^(1/3)<p≤sqrt(x), however, the cube p³ is omitted from CA and contributes positively to the remaining full tail. `geometric_finite_tail_plus_cube` reserves that actual term before bounding the finite exponent collection; `finite_correction_by_base` retains the exact exponent filter. The proved consequence `fullTail_ge_square_add_cubeFinite` is

    fullTail(x) ≥ squareFinite(sqrt(x),10^19)+cubeFinite(x^(1/3),sqrt(x)).

Ordinary finite Abel summation, with both source endpoint conventions retained, proves

    cubeFinite(w,y) ≥ .5/w²−2.29/(w²sqrt(w))−.5/y²,

using the same θ bounds and w=x^(1/3), y=sqrt(x). Convergence and the finite/full-prime transport are inherited actual proofs. `CubeAbel.lean` proves the integral and every boundary term rather than assuming a cube-tail coefficient.

Set u=x^(1/12). On the admitted band 7<u<40. `first_mertens_cube_profile_u` proves the whole real lower profile

    sqrt(x)*(A−logx−E)
      ≥ .01379001 + [.5/u²−2.55/u³−2.29/u⁴−2.5/u⁶]−2u⁶/10^19.

The bracket is at least .000229 on the complete interval [7,40], proved by the three exact rational segments [7,10], [10,20], [20,40]. The endpoint loss is below 2e−9, so `.014` follows strictly. This is continuous-domain mathematics, not a sampled curve.

The separate `MertensProfile.lean` keeps the original square-tail profile without recovering cubes:

    sqrt(x)*(A−logx−E)
      ≥ .01379001−2.55/x^(1/4)−2sqrt(x)/10^19−2/sqrt(x).

It gives `.00745/sqrt(x)` on the old band and `.00031/sqrt(x)` on the earlier full closed band [exp(21),10^19], reducing that analytic start by a factor exp(3). The cube theorem is the stronger margin result; the earlier-onset square theorem is a different Pareto point. No all-ray positive sign beyond the finite published inputs is asserted.

The copied `IEANTNAdapters.lean` is actually invoked by the new consumer. It instantiates the three existing Buthe.v1 conclusions, rather than inventing finite numerical suppliers.

## Nicolas: install the stronger actual baseline

Primary source: Jean-Louis Nicolas, *Small values of the Euler function and the Riemann hypothesis*, arXiv:1202.0729v2. Eq(1.3) defines beta=2+γ−logπ−2log2. Eq(1.9) defines f=exp(γ)logθ(x) times the finite product of (1−1/p). Eq(1.19) gives |W(x)|≤beta on RH. Proposition2.1, Eq(2.16), PDFp8, applies at x≥10^9 and yields the requested coefficient `2−beta−2.062/logx` for the negative log of f.

The paper itself has the stronger complete upper function in proof Eq(2.19), on x≥599. Its actual transported log-product lower coefficient is

    2−beta−(2+beta)/L−4beta/L²−sqrt(x)*L/[2(x−1)], L=logx.

`NicolasBaseline.lean` defines the actual prime product, f, all nontrivial zeros, their actual meromorphic multiplicities and W. It retains the exact original Eq(1.19) and Eq(2.19) as separately named literature contracts. The formal proof checks finite-product positivity, proves θ(x)>1, proves the f/reciprocal-product normalization and derives both the log-product lower inequality and a genuine relative-product consequence using log(t)≤t−1. There is no assumed arbitrary P, desired-margin predicate or unproved product identity.

This is import and verified adaptation of a stronger known full function. It is not credited as a new numerical record or an improvement over Nicolas. The old `1.876` is not the literature frontier. Exact decimal comparisons for beta require the elementary constant enclosures; the exact-beta theorem does not introduce a new numeric input merely to print a decimal.

## BFKNW Table13: a baseline normalization issue, separate from the new mathematics

The primary PDF p50 Table13 caption literally prints an extra `log(x)` denominator for the weighted Υ=A and Mangoldt weighted columns. For the first row [exp(1),exp(2)], Υ's constants are ell=−1.851 and L=−.293. Read literally, it would imply

    A(x)−logx−E < 1.851/[log(x)*sqrt(x)].

`Table13Check.lean` proves a source-independent exact counterexample at x=7: the actual error is greater than .4, while the printed upper expression is below .4. It also proves exp(1)≤7≤exp(2). The proof uses γ>1/2, positive correction terms for the actual primes2,3,5 and explicit elementary log bounds already proved in Mathlib. It uses no RH or external source premise.

This does not establish that the numerical table entries or headline theorems are false. The entries appear consistent with a sqrt(x) normalization, but that repair must not be silently substituted for the printed source. Eq(154), Lemma21 and the new `.014` proof do not use Table13. The source comparison requires an independent second pass before a final finding is reported. The current IEANTN package has no standalone Blueprint obligation for this table; the correspondence is the source-owned Mertens definition and the explicit new Table13Check source test.

## Reproduce and audit

From this directory, run `python reproduce.py --out /absolute/fresh/output`; for independent optimization modes run `python -O reproduce.py --optimize O --out /absolute/fresh/output-O` and the analogous `-OO` command. Use `--context` to relocate the pinned generic dependency paths. The compiler, Mathlib and generic commits must retain the exact identities in BUILD_CONTEXT.json. The script builds every application source into a fresh object tree and checks all 27 new theorem axiom closures. No inherited application object is needed.

`python exercise_controls.py --out /absolute/fresh/controls` executes 69 actual positive/negative CLI controls in normal/-O/-OO. Every one of the 18 source-module routes is independently corrupted and must be rejected. Acceptance uses explicit errors and strict duplicate-key parsing, with no assert or __debug__. Receipts are written atomically only after all checks pass. Historical failed compiles and rejected metadata remain in the separate run store.

The exact source-first boundary is absent for these new kernel-only results. Pinned generic library builds and compiler/runtime/OS/hardware contracts remain explicit. Named publication claims are theorem parameters, not axioms silently discharged by standard-only kernel output. Original published prime/zero computations were not rerun here.
