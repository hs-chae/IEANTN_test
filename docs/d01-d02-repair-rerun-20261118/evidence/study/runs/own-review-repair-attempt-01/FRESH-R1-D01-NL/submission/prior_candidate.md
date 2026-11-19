# D01: the additional assumption is redundant

**Main conclusion about premises.** Write B0 for the seven pinned originals, including the original QRH, at their stated trust tier. B0 already gives
\[
 |\psi(x)-x|<0.020\,x^{7/8}\quad(x\ge e^{200},\ x\text{ real}).
\]
Thus B0 entails the exact D01 hypothesis (whose coefficient of \(x^{7/8}\) is at least 625 on its domain). The strongest lawful consequence envelope **on any matched domain** is unchanged by D01, even if another lawful original-source use improves on the numerical portfolio below. This is implication, not experimental failure to see an improvement. We never assume full RH. This is not a blind independent B0 run.

**Both families, using B0 only.** See [Ramanujan](ramanujan.md) for the connected strict real positivity ray, its exact open lower endpoint with a certified bracket, and quantitative bounds, including a variable profile and higher-order rays. For example \(R(x)>x^2/L^6\) for \(L\ge42.65\), and \(R(x)>(1+14/L)x^2/L^6\) for \(L\ge47.25\). The real endpoint uses the finite integer component of the published Ramanujan computations at literature trust and a separate real join; the literal real endpoint in Platt–Trudgian Theorem 2 does not survive this check.

See [Mertens](mertens.md) for a pointwise envelope for each normalized product and both prime sums, signed errors, coefficient/onset tables, finite and analytic joins, and sharper inverse-square/cubic and spectral bounds. For example: coefficients \(0.10\) in place of \(0.20,0.30\) for the respective inverse-log envelopes with certified later onsets. For \(L\ge200\), both relative product errors and the reciprocal sum error are \(<0.0195e^{-L/8}/L\), and the log-weighted sum error is \(<0.0195e^{-L/8}\). The normalized constants in the spectral bounds tend from above to \(0.010445\), not a claimed optimal leading constant.

**File map and replay.** [psi.md](psi.md) proves the B0 all-real majorant. The application files prove the claims and give source locators, comparisons, failed attempts and limitations. The .out files are execution receipts, not external hypotheses. Set PYTHONDONTWRITEBYTECODE=1, work in the submission directory in non-login bash, and run:

    /usr/bin/python3.10 cert.py
    /usr/bin/python3.10 cert.py endpoint
    /usr/bin/python3.10 mcert.py
    /usr/bin/g++ -O3 -std=c++17 mertens.cc -o /work/mcert
    /work/mcert > /work/mertens-replay.out
    /usr/bin/python3.10 witness.py /work/mertens-replay.out

These are mathematical proofs with ordinary exact-integer certificates and some inherited source computations; neither Lean formalization nor source-first PV is claimed. The historical restored explore.py was not used as a certificate. See restart.md for execution and review status.
