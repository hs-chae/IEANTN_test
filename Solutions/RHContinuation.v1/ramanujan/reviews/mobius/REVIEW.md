# Independent Möbius review

Reviewer: Ramanujan continuation agent,2026-11-22. Reviewed exact source/receipt hashes are in REVIEW_RECEIPT.json. No mathematical defect was found in the written reciprocal/Stieltjes/Gamma/Perron mechanism or in the inspected full-function formulas. One pinned-primary locator correction is required. This review does not promote the written RH-to-M theorem to a completed Lean theorem or source-first PV.

## Actual declarations and source correspondence

The new written statement is RECIPROCAL_ZETA_DERIVATION.md§6: |M(x)|<1100000 x^(107/132), all realx≥1 underRH, and§7 gives |m(x)|≤6908000 x^(-25/132). The actual Lean theorem `RHContinuation.PerronPower.actual_M_from_three_enclosures` explicitly takes Perron45At plus three actual zeta-Mellin integral norm bounds. `WeightedMobius.weighted_power_candidate_consumer` additionally takes the actual AbelAt contract and the M power bound. These hypotheses remain unclosed. There is no standalone old Blueprint label for this new construction; its correspondence is the continuation signed/mobius module and the precise declarations just named.

Simonič2201.10771v1 PDFp17 Eq45/46 supplies the actual smoothing identity, ordinary endpoint discrepancy and Mellin argument. I reread that primary page. It is valid to derive a newσ=.75 contour argument rather than substitute into his finalσ=.98 constants. The written proof does supply the needed new horizontal-edge argument. The primary conditional identity is separate from the new numerical bound.

## Reciprocal chain and normalization

The paired HasSum normalization atw=.5 is legitimate because actualξ(.5) is nonzero and the functional equation givesξ'(.5)=0. The shifted digamma identity absorbs the1/s term; it is consistent with the completed-xi derivative. Pairing positive and negative zeros gives2(s−.5)/((s−.5)^2+γ²), including multiplicity. The paired/subtracted family is locally uniformly O(γ^-2); zero count proves the dominating sum summable. Horizontal real-part integration therefore produces exactly halfQ, with no unknown exponential normalization. This step uses the actual completedxi and actualζ, not an artificial function with a chosen zero list.

ForN=m+E, m(0)=7/8 andf_t(0)=2k(t), so the Stieltjes boundary is7k(t)/4 inQ, and7k(t)/8 inhalfQ. The even full-line main integral has exactly1/(2π). The Poisson logarithm contour has residueLog(t+i(v+η))/(2i), hence real-axis integralπLog; the stated1/π normalization follows. Lettingη↓0 is justified by the local logarithmic integrability and log(u)/u² tails, then positive finite-v Fubini givesJ. No factor2 is lost in either passage.

The translated variation sum is at most2k0. AboveU=2(t+1), the derivative majorant18d/u³ and the concave-log tangent produce the stated0.9d/[U(U+2)] after the halfQ factor. The broad low-height count bound follows fromN(1)≤2 and0<m(u)<7/8 on(0,1); no unpublished individual-zero table is needed.

The Gamma identity's bracket is in[-1,0], so its absolute remainder is≤1/Re z. The horizontal Gamma ratio contributes log(σ1/σ0), and the favorable Poisson/Gamma main-term cancellation has the correct sign. The polynomial ratio is≤max(1,(1−σ0)/(σ1−1)). Atσ=1,t=0 the completedxi/reciprocal limit must be used; the written proof explicitly avoids substituting totalized pole values. This is an aligned domain treatment.

Forσ0=.75,σ1=1.05 the prefactor147, k0=2log2.2<1.58 andε=.32 are consistent. U≥2 bounds the tail by.9d/8, giving(G). Splitting t≤1 andt≥1 with2t+4≤6max(1,t) yields(H), C150000. The bounds hold uniformly through the entire horizontal strip by monotonicity inσ; above1.05 the elementaryEuler envelope≤21 applies.

## New contour and Perron transfer

On the moved stripRe s≥.75, RH makes1/ζ holomorphic, including its removable zero at1. Poles ofs(s+1) are outside. The uniform reciprocal envelope gives horizontal decayO(T^(.32−2)), so the horizontal integrals vanish for each fixedpositive x,h. The sameε<1 gives absolute convergence of the vertical integral. The ordinary finite smoothing discrepancy is≤h(h+1) before dividing byh, matching SimoničEq46 at integer endpoints.

Withh=x^κ,V=4x/h,κ107/132 andx≥1, one has1≤h≤x,V≥4. The low/middle/high norm coefficients in§6 have the correct both-sign factor and1/(2πh) normalization. The high coefficient2^(σ+2) becomes2^σ4^ε afterV substitution. The exponent identityσ+(1−κ)ε=κ is exact. Bounding2^σ<2,π>3,4^ε<2 gives a total coefficient below1.1million with slack. The weighted Abel conversion has1+1/(1−κ)=157/25 and exact coefficient6908000. The explicit Lean remainder contracts are therefore appropriate partial statements, but are not discharged by this review.

## Actual full literature frontier

I read JLTv3 PDFp27 ThmA1,p28 PropositionA3 andp32 Table1: all seven OUTPUT(k,cM,logxM) rows in compare_frontier.py match. They are not the A,α input columns. RZA2408.05969v2 PDFp1 Thm1.1 is exactly(.006688logx−.039)x/log²x forx≥1798118, as used; this is stronger than quoting only the abstract. Simonič2021 PDFp2 Eq9/11 andp3 Table1 confirm the full subpower function and the double-exponential onset translation. The formula inL is correct, and it eventually beats the fixed-power candidate. The claimed sign bracket is labelled only a sign bracket, not a unique or continuous dominance interval. Pointwise comparisons are not an exhaustive global literature optimum.

The Lee–Leongv5 full c1,c2,c3 formulas and all15 row constants/domains match PDFp4 Table1 andp5 Thm2.2. However, current comparison labels refer to Eq18/19/20 plus21/22/23. In the pinned PDF the three final inequalities are Eq17/18/19, and c1,c2,c3 are unnumbered immediately above. Eq21 on PDFp6 defines aw,bw, not these M bounds. This is a provenance locator defect only: the numerical formulas are aligned. It was sent to the signed author and root, who are preservingV1 and regenerating correctedV2. The actual pinned PDF identity must take precedence over differently numbered live HTML.

## Limits

No independent Arb re-execution or all-source mathematical census was performed. The comparisons are to the explicit catalog and legitimate common domains; no universal dominance or best-known claim follows. Written validity does not close the actual Lean complex-analysis obligations, nor does ordinary numerical comparison constitute source-first PV.
