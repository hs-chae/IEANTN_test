# Independent octic mathematical review

Reviewer: Ramanujan continuation agent, 2026-11-22. Scope: the exact file hashes in REVIEW_RECEIPT.json. This is an independent written mathematical/source review, not a completed Lean analytic proof or source-first PV. No mathematical defect was found in the reviewed chain. One inherited primary citation needs explicit correction, already known in the earlier source audit.

## Exact source identity

The proposed written result is OCTIC_PROOF.md, fixed C=2.15 and family 1.03≤C≤16, every real u≥exp24. Its actual Lean counterpart is OcticConsumer.lean importing the EvenKernel.lean conditional mathematical interface. There is no standalone published Blueprint label for this post-lock construction; its correspondence is the continuation parabolic module. Those Lean consumers retain EF, density, costs and geometry assumptions, and are not RH-only Lean closure.

The source actually supporting the zero count is Brent–Platt–Trudgian, *The mean square of the error term in the prime number theorem*, JNT238 (2022), Corollary1, printedp743 (PDFp4), DOI10.1016/j.jnt.2021.09.016. It states N(T)=T/(2π)log(T/(2πe))+7/8+(0.28ϑ)logT, T≥2π, |ϑ|≤1. This gives the intended M with +7/8. I read the actual publisher PDF, SHA256 in the receipt. The actual Lee–Nosal v4 Eq(8), PDFp3, instead prints +7/8 *inside* |N−main+7/8|. The current argument must cite BPT directly rather than imply literal agreement with that displayed Lee–Nosal line. This correction leaves the mathematical bound used in the octic derivation unchanged. The original BPT result has a published finite interval-arithmetic input up to7.7·10^8; it is a literature assumption, not a new independent rerun here.

## Fourier and continuous quadrature

The transform formula follows by integration by parts from ∫[-1,1](1−s^8)cos(ys)ds. Direct differentiation gives exactly the listed derivative coefficients. From this integral, |f|≤16/9, f≥16/9−8y²/33 and |f'|≤16y/33. Splitting at6 gives the stated variation integrals: the small-y ordinary part is96/11; the positive-log part is(16/33)(18log6−35/4). The explicit power tails in octic_scalars.py have the correct exponents and coefficients.

Directed dyadic addition, multiplication, inversion and powers enclose real arithmetic. The exponential remainder is a geometric bound on the first omitted Taylor term; the log atanh remainder and reduced trig alternating remainders are sound on their checked domains. Resetting trigonometry every1000cells avoids accumulated interval growth; the update uses simultaneous old sine/cosine values. The log tangent is a valid upper bound because log is concave, and only x>1 cells use it. No float affects acceptance.

For h=.001, midpoint error hV/2 bounds the mass, and h(Vlog+W)/2 bounds the positive log moment by the integrated variation argument. The negative-log contribution on[0,1] has the correct inequality direction, yielding −16/9+8/297. The |cos| zero-mean primitive is periodic and bounded by1; integrating y^-2 by parts gives 2/(πH)+2/H², including the H boundary. Remaining mass tails and all log tails are valid absolute majorants. The output rows enclose an upper-bound expression; they do not provide lower bounds on actual Fourier moments. The source explicitly makes that distinction.

## Explicit formula and zero signs

Using the twice-integrated explicit formula with test w(t)=t^-1/2 g(log(t/x)/δ), supported away from1, the RH zero integral is exactly exp(iγlogx)δf(δγ). There is no extra √x. The endpoint value is zero; the derivative jumps must be included when twice integrating by parts. The absolutely convergent integrated zero series and piecewise C² test justify this operation, and the resulting |γ|^-2 Fourier tail is summable against the classical zero count.

Both ordinate signs yield the factor2. Stieltjes integration against N−M has lower boundary R(0+)=-7/8, hence boundary constant (7/8)f(0)=14/9 inside the doubled δ term. The density contribution is A log(1/(2πδ))+B. In the allowed range this logarithm is positive, so substituting an upper bound for A preserves direction. The bound log⁺(y/δ)≤log(1/δ)+log⁺y supplies the discrepancy integrals. N(12)=0 follows from the upper count <1 and integral full multiplicity; eta positivity rules out γ=0. No individual-zero table or spacing input is added.

The constant log(2π) disappears under dψ. The trivial density is −1/[t(t²−1)], giving the stated negative correction ≤2δ/[√a(a²−1)]. No sign was lost.

## Prime powers and all-real conversion

For k≥2 the count of possible integer prime bases is at most1 plus the root interval length. The bound 2x^(1/k)sinh(δ/k)≤(2δ/k)e^(δ/2)√x, the per-prime weight ≤e^(δ/2)(L+δ)/(k√x), Σ1/k²≤1 and Σ_{2..K}1/k≤logK give exactly Q in the proof. Counting all bases as primes is a safe upper bound.

The maximum ordinary-prime weight is log(a)/√a because a>exp2 and g≤1. Thus dividing the lower weighted sum proves the displayed actual count, and the strict lower inequality survives. For the interval width, each elementary factor is ≤1+δ on the stated δ/L range, and (1+δ)^3≤1+4δ for δ≤1/4. The certified 4CLδ<2 gives b−a<C√a loga. Finally L↦L−δ is continuous, strictly increasing, starts below24 and tends to infinity, so it covers every logu≥24. This is a continuous proof, not interpolation of samples.

The uniform family cap and costs use their largest C and smallest L; L²e^-L/2 and Llog(2L)e^-L/2 decrease for L≥24. The logarithmic bonus is minimized at C=1.03,L=24. The slope identity 8C/9−.911 is exact and positive on the full family. At C2.15 it is9001/9000. These checks support the stated bounds at their written-proof tier.

## Limits of this review

I inspected the exact rational implementation and existing accepted-certificate semantics but did not rerun a separate200000-cell replay. The independent review is not a source-first verification of Python or a formal proof of the EF pairing/zero-count contracts. Nothing here upgrades conditional Lean consumers to RH-only formal results. The published comparator/novelty discussion was not audited beyond its stated caution; no best-known result is certified.
