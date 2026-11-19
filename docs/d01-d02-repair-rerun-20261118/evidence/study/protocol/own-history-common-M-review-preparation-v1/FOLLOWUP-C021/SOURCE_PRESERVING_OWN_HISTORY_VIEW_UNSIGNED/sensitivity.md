# Later-stage sensitivity audit (not the current D01 contract)

The supplied current INPUT_CONTRACT.json has exponent 7/8, not 27/32. No 27/32 statement is invoked in the D01 results. Both of my own historical artifacts were supplied and replayed; the following records what the repaired proofs would certify under the distinct counterfactual H' with exponent 27/32 and the same coefficient, log-power and threshold, in addition to the same B0. It is a conditional mathematical comparison, not an independent blind baseline and not evidence that H' is true.

The log-derivative argument in power.md would imply beta<=27/32. Use this strip for the common-grid constructions there. The better pointwise psi bound is justified even on [e^80,e^200), by a zero-free strip consequence of an assumption given only on the later ray. The step and continuous relative-error envelopes are strictly smaller than their B0 counterparts at every t>=80. This follows by adding the positive test-function increments over the interval of sigma beyond 27/32 for the B0 envelope. It is not a comparison of two non-nested sample grids.

## Conditional gap margins

Use ram.py sensitivity and the row convention of ram-new.md. The plateau switch y_b moves to 167.96, its validity being tested using the improved C_b there. Both the earlier switch and the faster exponential decrease make the plateau radius no larger at any z. Consequently the adaptive G may be maximized with the B0 function, never weakening the lower envelope; before either switch is effective the input gives no such improvement. The positivity onset is already sharp in B0 and cannot improve. The positive finite inequality joining the old integer result is not a separate causal success of H'.

At fixed degree 6, the conditional program verifies the following higher constants (see checked row list in ram.py and stdout):

    t=48        c=40
    t=48.75     c=70
    t=49        c=80
    t=50        c=82.4
    t=176       c=124
    t=186.6     c=145

At fixed quadratic coefficient 145 the onset is 186.6 instead of the current B0 proof's 219 and the older conditional 190. The cubic coefficient beyond the 145 profile is 500 from 190 and 1412 from 212 (B0: 253 for 1412). Beyond that, 13985/t^4 holds from 238.1 and another 145450/t^5 from 267 (B0: 289 and 324). Finally the exact coefficients at degrees 10, 11, 12 and 13 hold from t=303,322,350,385 respectively, versus 360,397,432,480 in B0. Earlier quantitative slopes and the exact root remain the B0 bounds. Exact closed-cell comparisons and analytic continuations are the same as for b=7/8; only the point input for the plateau changes.

## Conditional Mertens margins

With b=27/32 the spectral transfer of mertens-new.md changes both the inherited high-ordinate tail and the point majorant. A joint constant .262 in the x^(-5/32) scale (add 1/t for both products and |u|) holds on the entire closed ray x>=10000, using the clipped finite branch and the analytic joins from mertens_new.py. The convex middle branch ends at t=167.8 rather than 186. Separate later constants .21825, .170, .130 and .117 hold from t=200,300,1000,50000 respectively. The earlier conditional .227 bound at t=200 was a psi coefficient and would have paid an additional integral loss for Mertens without the spectral argument. Here the point and tail terms are combined directly, with the positive spill controlled separately.

Compare powers in their actual relative coordinates, not by ranking scalar coefficients: .262 times exp(-5t/32) is smaller than .01325 times exp(-t/8) exactly when t>32 log(.262/.01325) on shared domains. More finely the common-grid C_b(t)*exp(-(1-b)t) plus J_b is strictly smaller for the narrower strip than for the wider one for all t>=80 where used, and the positive-kernel integrals preserve this comparison. The finite, CH2 and other original branches are retained by intersections in both treatments, so no claim that a new branch is selected at every point. No improvement in the limiting exponent beyond 27/32 was justified under H'; its boundary-zero allowance is unchanged. The exact finite P/Q roots and the no-QRH/no-contract finite tables are not conditional discoveries.
