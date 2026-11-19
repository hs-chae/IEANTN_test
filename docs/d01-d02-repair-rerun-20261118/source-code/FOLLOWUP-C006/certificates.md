# Certificate review and reproduction

Use a non-login /bin/bash, then from /work/submission with bytecode generation disabled:
```
export PYTHONDONTWRITEBYTECODE=1
/usr/bin/g++ -O3 -std=c++17 count.cpp -o /work/d01-count
/work/d01-count
/usr/bin/python3.10 analytic.py
/usr/bin/python3.10 ramanujan.py
/usr/bin/python3.10 mertens.py
/usr/bin/python3.10 mertens.py scan
```
Do not set PYTHONOPTIMIZE or use python -O; assertions are proof obligations. The factor of pi in analytic constants is the ordinary circular constant. The optional 'explore' arguments are diagnostic only. Logs in evidence.txt are replay output; any printed decimal interval is diagnostic, with the actual comparisons performed on integer endpoints. Exact rational bounds and hypotheses are in the claim files and source; no displayed precision is used as a new premise.

## Independent arithmetic audit of certlib.py

An interval (lo,hi) represents endpoints lo/S, hi/S, S=10^36. Fractions are enclosed via integer floor and ceiling. Addition, sign reversal, multiplication (extreme corners), positive-denominator division (monotonic endpoints in numerator, extreme denominator), and powers by repeated squaring all use outward operations. Decimal strings are exact rationals, not floats; only the repr function displays machine floats.

For a rational in [1,2], compute a lower log using \(2\sum_{j\ge0}z^{2j+1}/(2j+1)\), \(z=(a-b)/(a+b)\in[0,1/3]\). This series follows by integrating the geometric series. In units of 1/S, rounding \(z\) costs <1; its squared lower approximation costs \(<1+2/3<2\). Each monomial recurrence costs at most \(E/9+2/3+1\) if the previous error is \(E\), since the true power is at most 1/3. Starting at <1 this stays below 2. Each divided term costs at most \(1+2/(2j+1)\le3\); the doubled sum costs at most \(6n\). The omitted geometric tail bound \(2z^{2n+1}/[(2n+1)(1-z^2)]\) is \(<1/S\) for \(z\le1/3,n=42\) or \(z\le1/512,n=7\). The dyadic reduction and the anchor \(1+j/256\) leave residual ratio \(<1+1/256\), so \(z<1/512\) for the local seven-term calculation. Each individual log error is thus \(<512/S\), and lnq accounts for the sign of the log-2 multiplier.

For exp, monotone endpoint evaluation reduces nonnegative arguments to [0,1] by repeated halving, sums through degree 42 then rounds the upper endpoint by \(1/S\) for the remaining tail, which is \(\le (1/43!)/(1-1/44)<1/S\). The appropriate integer power restores the original argument. Negative endpoints use reciprocals. Machin's identity follows from the tangent addition formula in the correct quadrant; the alternating arctangent tails after 31 terms are \(<1/S\), including parameter 5. For gamma, each unit trapezoid error for \(1/t\) after \(n=100000\) lies between zero and \(\max(2/t^3)/12\) by the integrated interpolation error. The total tail is at most \(1/[12(n-1)^2]\) by integral comparison, giving the interval correction to \(H_n-\log n-1/(2n)\). No system transcendental or floating sample is needed.

## Source and process boundaries

All seven original PDF and text files are bound by RUNTIME_PATHS.json; all fourteen listed hashes matched SOURCE_INDEX.json. The text extractions and original page locators were used offline. The allowed project environment is not needed for these proofs. New analytic arguments and normal execution certificates are supplied here; the original finite computations and analytic theorems are reused at their inherited trust. No external code/data or delegation, no claim of Lean verification, and no claim of C++ source-first PV. The command history from the earlier interruption was not replayed wholesale. Initial pwd was successful, ls was not on PATH, diagnosed with exit 127; Python read the requested files directly. The locale warning in tool output did not change any checks.


## Repair continuation
The current combined command is /usr/bin/python3.10 replay_repair.py from /work/submission in the same non-login shell. In addition to the above, it runs bias_repair.py, density_repair.py, ramanujan_orders.py tight, and comparison_repair.py. The mathematical linkage and the opt-in inherited normalized source tier are in repair.md. The displayed prior evidence.txt is preserved; repair-evidence.txt is the current staged replay transcript. Caught failures are exploratory tighter targets, not dependencies of any claimed row. New interval leaves are established by the same exact arithmetic as the previous checks.
