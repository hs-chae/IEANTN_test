# D01 repair and improvement: both families

**Scope.** Write (t=log x), (h=x^2/t^6), and let **B0** denote the seven bound originals at their original trust, including OpenAIQRH Theorem 1.1. The exact current extra assumption is

    (H)  |psi(x)-x| <= x^(7/8)*(log x)^2/64   (every real x>=exp(200)).

All statements below are for real arguments unless otherwise indicated. No full RH is assumed. Computations are ordinary, with directed rational arithmetic; no kernel proof or source-first program verification is claimed.

**Attribution and comparator.** In fact **B0 proves H**. For example, the density-free proof in `D01_density.md` gives 0.0045*x^(7/8)*t^2 for (t>=185) from the original QRH strip, FKS Theorem 3.2 and a reciprocal-ordinate bound. The sharper new proof in `power.md` gives less than (1/50300) of the supplied majorant on its entire ray. Consequently B0 and B0+H have the *same* mathematical consequences, not merely the same observed scores. The direct-H term can be inserted into the corresponding positive-kernel transfer formulas; it does not improve the installed B0 envelopes on its domain. H also provides an alternative proof of the strip if one drops the QRH paper, by meromorphic continuation of the log derivative (see `D01_density.md`); this is a premise tradeoff, not a gain over cumulative B0.

## Ramanujan

See `ram-new.md` and `ram.py`. Let (n=38358837682). The unique root (r) of
[
 e*r*632207037/log r=1644673232^2
]
in ((n,n+1)) satisfies
[
38358837682.217926<r<38358837682.217927,qquad R(r)=0,qquad R(x)>0quad (x>r).
]
This is the sharp strict real positivity boundary; (n+1) is the least sufficient integer onset. There is a linear lower margin (67623427(x-r)) strictly below (R(x)) on ((r,n+1]). The original small real wording cannot be used on ((n,r]); exact counts and monotonic transfer justify the valid integer restriction and the join. No new verification of the source's large integer segment is claimed.

New B0 quantitative examples: (R/h>.05) from (t=36.88), (>1/2) from 38, (>1) from 40.23. The (1+14/t) threshold moves to 47.25. The coefficient of (t^{-2}) beyond (1+14/t) is (20.5) from 47.65, (112) from 200 and (145) from 219. A further (1412/t^3) holds from 253, (13985/t^4) also from 289, and (145450/t^5) also from 324. Continued rows retain the exact positive terms through degree 13 (the t^(-9) term in R/h, from t=480). These are strict on inclusive real rays, with other tradeoffs and adaptive functions retained in `ram-new.md`. All these examples are improvements in the derived B0 portfolio, not effects of H.

**Secondary, without QRH or H:** the improved range is the union of (r,exp(754)] and [exp(3039.2),infinity). There are new late margins even with this restricted corpus. The no-QRH middle remains open in this work; it is not a gap in the complete B0 result.

## Mertens

See `mertens-new.md`, `mertens_new.py` and `sieve_repaired.c`. For ((P,Q)) use the two unsigned normalized relative deviations; for the sums use the absolute signed deviations from (loglog x+M) and (log x-B_3), with Dusart's constants. From x=420000 the two products and unweighted sum each have a strict error bound 0.01325*x^(-1/8)/t. The weighted sum has the strict bound 0.01325*x^(-1/8) from x=550000. Later caps, e.g. (.01241) from (t=200) and (.00668) from (t=100000), sharpen these on their respective domains. The analytic pointwise intervals distinguish the direction of the error and which reciprocal is used; a logarithmic upper radius is not itself a relative radius.

A separate logarithmic sequence extends the finite table to smaller caps, e.g. (.0105) from (x=10^{10}) and (.0000000370) from (t=70), dividing by (t^3) for products/unweighted and (t^2) for weighted. Take the pointwise best applicable bound, not the new power envelope alone: the latter crosses the old logarithmic tolerances. The original coefficient .2 for (P) alone has sharp closed onset in ((2278381.575,2278381.577)); for (Q) or both the sharp onset remains in ((2278381.710,2278381.712)). Equality holds at the exact roots. The other sharp roots and strong no-QRH finite/analytic results are preserved. The missing auxiliary segment ([10000,10007)) has been repaired and replayed; the unchanged historical stdout alone was not evidence for that segment.

## Inheritance and separate sensitivity audit

Both of my historical submissions, D01 CAND-009 and D02 CAND-006, are explicit inheritance. The flat `D01_*` and `D02_*` files preserve their exact bytes. Historical naming, scope and some comparisons refer to the historical environment: no old project, other arm, or coordinator repair was accessed. This is not a fresh blind baseline. D02's stronger exponent (27/32) is **not** in the current contract. Its own original evidence was replayed, its input-independent outputs are used where proved, and a separately labelled (27/32) sensitivity proof is included for the later stage. No (27/32) conclusion enters the current D01 portfolio.

Read `replay.md` for execution, failure diagnostics and the review boundary. Search the compound envelopes in the two claim files and `power.md` for formula-level statements; this index is not a substitution for them.
