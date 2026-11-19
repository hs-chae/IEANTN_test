# D01 both-family submission

**Premise result:** under the pinned originals (B0), the exact additional D01 premise follows with strict slack: .0045 in place of 1/64 on its full real domain. See common.md for the short proof and the much sharper density versions. Thus there is no additional arithmetic improvement from this premise in either family, even relative to the full lawful B0 consequence envelope. No independent blind baseline was run or claimed.

**Ramanujan:** ramanujan.md proves a connected strict sign ray above the sharp real edge (using literature trust for the old early integer checks); it corrects the printed real endpoint. The new analytic argument alone proves \(R(x)>.03 x^2/\log^6 x\) from \(e^{36.85}\), \(R(x)>x^2/\log^6 x\) from \(e^{42.85}\), and many stronger profiles, including sixteen coefficients from \(e^{840}\). It includes a non-polynomial pointwise bound, an arbitrary-order construction, and separate finite-strength windows.

**Mertens:** mertens.md gives separate pointwise envelopes for both products and two sums, finite block bounds, improved constants at matched onsets and exact real crossings at the original four constants. The analytic bridge and finite certificates overlap. From \(L=\log x=200\) the product and reciprocal-sum errors are at most \(.019354e^{-L/8}/L\) and the weighted prime-sum error at most \(.019354e^{-L/8}\), with earlier and later constants and a decreasing functional envelope. This uses a fixed-cutoff oscillatory transfer with an explicit bound for the truncation strip, not a grid extrapolation.

All new results are input-independent secondary results. “No additional improvement” in STAGE_STATUS refers to the effect of D01, not lack of proved arithmetic conclusions. Independence and source-first PV are not claimed. The larger published early Ramanujan integer calculation is not replayed; the new arithmetic is replayable.

## Replay

From /work/submission use a non-login /bin/bash:

    /usr/bin/python3.10 -B replay.py

The script compares outputs byte-for-byte against the saved files, keeping compiler and generated files under /work. It uses only the bound offline originals to validate the source hashes. It calls the following:
* certify.py: rational domination, density, and real-cell strict gap inequalities; gap_envelope.txt is the final transcript. PASS means valid at the stated parameters; FAIL is an unsuccessful trial rather than a detected arithmetic counterexample.
* edge.py: exact unit-interval Ramanujan sign and prime counts, edge_result.txt.
* mertens_cert.py: rational analytic joins and exponential coefficient checks, mertens_result.txt.
* finite.cpp compiled with g++ -O3 -std=c++17 (no assertion-disabling flag): exact-integer interval sieve and proof probes, finite_final.txt.
* cutoffs.py: exact refinements at the original Mertens margins, cutoffs_result.txt.

gap_attempt.txt, gap_refined.txt and gap_final.txt are historical research runs, not the transcript of current source; use the final envelope and proofs for claims. The historical restored LOCK is retained separately. No private reasoning transcript is included.

