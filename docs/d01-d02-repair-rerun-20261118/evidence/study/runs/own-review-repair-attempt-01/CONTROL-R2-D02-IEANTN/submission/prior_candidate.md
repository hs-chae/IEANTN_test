# FOLLOWUP-D02 — research portfolio for independent review

**B0** is the full seven-original packet. **B1** adds exactly the hypothetical direct Chebyshev estimate in INPUT_CONTRACT.json, on the stated all-real ray starting at $e^{200}$. The paired B0 results below are within-method reconstructions, not an independent blind baseline.

| Family | Main result under the additional input | Independent B0 results preserved |
|---|---|---|
| Ramanujan | The $1+14/L+100/L^2$ normalized margin is supported from $L=172$ rather than the reconstructed $200.1$; at $L\ge49.1$ the certified $L^{-2}$ coefficient rises from 7 to 78 with the first two terms fixed. The full order-26 profile starts at $L=724$ rather than $939.5$. | Analytic positivity already from $L=36.9$, joining the inherited finite computation. The actual permanent real sign boundary is $38358837682+u$, $0.217926365<u<0.217926366$; the left endpoint is open. The published literal real onset immediately above the integer counterexample is false. |
| Mertens products and both prime sums | Improved power $x^{-5/32}$ instead of the reconstructed $x^{-1/8}$, with a further $1/L$ for the product relative errors and the reciprocal prime sum. At $x\ge e^{200}$, clean coefficients are .260 and .01880, respectively, for these two powers. Fixed-error onsets also improve; see the portfolio. | Non-strict envelopes $0.0223/L^3$ for both product relative errors and the reciprocal sum, and $0.0223/L^2$ for the weighted sum, with certified real onsets in the range $6.05\cdot10^8$ to $6.97\cdot10^8$; earlier onsets at the original coefficients are also retained. |

Here $L=\log x$. The normalized Ramanujan margin means $L^6R(x)/x^2$; all quoted margin relations are strict, and the $L$ thresholds are inclusive. The fixed exponent gain is obtained by deducing a zero boundary $27/32$ from the new hypothesis, not by dropping the available $7/8$ QRH theorem or by using the raw direct estimate below its domain. The high-zero transfer for Mertens retains oscillation before applying absolute values.

## Proof and evidence index

* [spectral.md](spectral.md): exact premises, source locators, density and explicit-formula proof for both caps.
* [ramanujan.md](ramanujan.md): real endpoint correction, quantitative and high-order whole rays, stronger pointwise envelope.
* [mertens.md](mertens.md): both signed product conversions, both prime sums, finite and analytic joins, coefficient/onset tradeoffs and pointwise minima.
* [notes.md](notes.md): reproducibility, trust tiers, serious attempts and remaining bottlenecks.
* [restart.md](restart.md): final state and next useful independent checks.
* LOCK.json binds all payloads; STAGE_STATUS.json records the research-stage assessment, not independent review.

No theorem here infers an entire real ray from exploratory floating samples. New finite joins use enclosed blocks, exact prime-jump checks, or monotonic tail reductions with verified endpoints.
