# Prime reciprocal constant from the stated input

## Result (mathematical proof; Lean status below)
Put A=exp(300), C=9354674/10^9, R(t)=pi(t)-Li2(t), with precisely the definitions in TaskDefinitions.lean. Assume only
Epi(t) <= C t^(-1/8) for every real t >= A.
There is a real B such that H(x)-log(log x) tends to B as real x tends to infinity, and for **every real x >= A**,

|H(x)-log(log x)-B| <= C x^(-1/8)/log x + C integral_x^infinity t^(-9/8)/log t dt
 <= 9 C x^(-1/8)/log x.

All powers here are real powers. B is not identified numerically. In fact

B = -log(log 2) + integral_2^A R(t)/t^2 dt + integral_A^infinity R(t)/t^2 dt.

The integrals with finite limits are ordinary Lebesgue integrals (equivalently Riemann integrals here); the last integral is absolutely convergent. No prime-error input below A is used.

## Proof
For x>=2, set N=floor(x) in the natural numbers and let P be the finite set of primes <=N. For every p in P,

1/p = 1/x + integral_p^x dt/t^2.

Sum this finite family. Interchanging a finite sum and integral gives

H(x) = pi(x)/x + integral_2^x pi(t)/t^2 dt.                 (1)

Indeed, for 2<=t<=x the number of p in P with p<=t is exactly pi(t), since t<=x. The equality of the integral is unaffected by values at its finitely many endpoints. This derivation includes the prime 2 and includes primes exactly at x: at x=p the new contribution in the integral has zero length, while the boundary term gains 1/p. The count equals Nat.primeCounting(floor(t)) because n<=t iff n<=floor(t) for natural n and nonnegative real t. Thus (1) concerns the actual definitions, not a proxy.

On [2,x], Li2 is continuously differentiable with derivative 1/log t. Integration by parts, using Li2(2)=0, yields

Li2(x)/x + integral_2^x Li2(t)/t^2 dt
 = integral_2^x dt/(t log t)
 = log(log x)-log(log 2).                                (2)

Subtract (2) from (1):

H(x)-log(log x) = -log(log 2) + R(x)/x
                  + integral_2^x R(t)/t^2 dt.             (3)

Local integrability is automatic: on any compact subinterval of [2,infinity), pi is a bounded finite step function, Li2 is continuously differentiable, and t^(-2) is continuous.

For t>=A we have log t>=300>0 and t>0. Multiplying the given Epi inequality by the positive t/log t gives

|R(t)| <= C t^(7/8)/log t, hence
|R(t)/t^2| <= C t^(-9/8)/log t.                           (4)

This use is restricted to t>=A. Since log is increasing,

integral_x^infinity t^(-9/8)/log t dt
 <= (1/log x) integral_x^infinity t^(-9/8) dt
 = 8 x^(-1/8)/log x                                      (5)

for all x>=A. The last equality follows by integrating the derivative of -8t^(-1/8) and taking its limit at infinity. In particular the absolute integral from A converges. On the finite interval [2,A], local integrability already suffices; it does not require any error estimate. Thus B above is well-defined.

Splitting the absolutely convergent integral at any real x>=A in (3) gives the exact identity

H(x)-log(log x)-B = R(x)/x - integral_x^infinity R(t)/t^2 dt. (6)

The triangle inequality, (4), and (5) prove the displayed whole-ray bound, including all prime endpoints. Finally x^(-1/8)/log x tends to zero (it is bounded above by x^(-1/8)/300 on this ray), so (6) or the bound implies the asserted real-variable limit. This establishes existence and the explicit constant 9 from the sole stated analytic input.

## Formalization status
The accompanying Lean source is a partial formalization, not a kernel proof of the final asymptotic theorem. Its exact checked scope and remaining obligations are recorded after compilation below. The mathematical result above is proved by the displayed derivation, but is not described as fully Lean-checked or as source-first program verification. No numerical experiment is used.


### Checked scope and exact remaining formal obligations
`Formal.lean` compiles successfully under the pinned Lean. In particular it proves:
* `count_indicator` and `reciprocal_indicator`: the prime-indicator sums are exactly the supplied pi and H.
* `prime_partial_summation`: (1) as a set integral on (2,x], for every real x>=2, from Mathlib's proved Abel summation theorem, with the indicator of **actual natural primes**. It assumes no PNT input.
* `Li2_hasDerivAt` and `Li2_partial_summation`: the derivative and exact identity (2), preserving the offset at 2.
* `pi_weight_integrable`, `Li2_weight_integrable` and `residual_identity`: finite-interval integrability and (3), for every real x>=2, unconditionally.
* `boundary_error_on_ray`: the sole PNT input, with exactly its exp(300) threshold, implies |R(t)/t| <= C t^(-1/8)/log(t) throughout that ray.

The remaining Lean obligations are **only mathematical-only here**, not assumptions of any claimed kernel theorem: derive integrability of R(t)/t^2 on [A,infinity) by domination using the input; prove the improper integral estimate (5); define B and split its integral to obtain (6); take the real atTop limit and combine to obtain the final existential bound. These steps are proved in the readable argument above, but no final Lean `exists B` theorem is claimed. In particular no arbitrary-function consumer theorem is substituted for the arithmetic goal.

The intended final theorem has hypotheses exactly
`hPNT : ∀ t : ℝ, Real.exp 300 ≤ t → Epi t ≤ C * t ^ (-(1:ℝ)/8)`
and conclusion that there exists B with
`Filter.Tendsto (fun x : ℝ => primeReciprocal x - Real.log (Real.log x)) Filter.atTop (nhds B)`
and, for every real x>=Real.exp 300,
`abs (primeReciprocal x - Real.log (Real.log x) - B) ≤ 9*C*x^(-(1:ℝ)/8)/Real.log x`.
This signature is a specification, not generated/checked proof source.

### Input source compatibility and reproducibility
`TaskDefinitionsInput.lean` preserves the exact supplied file. Under this compiler, its final `def C : ℝ` fails code generation because real division is noncomputable. `TaskDefinitions.lean`, used for the proofs, changes **only** `def C` to `noncomputable def C`. No expression, constant, domain or normalization changes; this is a code-generation annotation, not a mathematical hypothesis. `verify.py` reproduces that original diagnostic and then compiles the annotated definitions and proofs. `compile.log` records the exact commands, exit codes and diagnostics. The four printed theorem axiom reports contain only standard Mathlib/Lean foundational axioms (`propext`, `Classical.choice`, `Quot.sound`), not `sorryAx`. No new axioms, `sorry`, `native_decide`, numerical testing, external search, or executable-source verification claims are used.

Run from this directory: `/usr/bin/python3.10 verify.py`.
