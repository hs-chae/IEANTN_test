# Certified normalized-gap portfolio

On each listed real log domain the assertion is \(G(L)>m(L)\), hence
\(R(x)>x^2m(L)/L^6\). The strict real positivity ray \(x>r\) with
exact \(r\) is separate (see `ramanujan.md`). The table's ray
onsets are sufficient, nonnecessarily optimal for their positive
margins. Take the pointwise maximum of all branches on their own
domains, including \(\mathscr G\) from the proof.

## Fixed margin and fixed onset comparisons

| inclusive log onset | constant margin valid on the entire ray |
|---:|---:|
| 36.6 | 0 (the inherited-computation join in fact extends to the exact earlier root) |
| 36.7 | .065 |
| 36.8 | .10 |
| 36.99 | .20 |
| 39.61 | .25 |
| 39.7 | .27 |
| 40 | .385 |
| 40.5 | .50 |
| 41 | .64 |
| 41.93 | .80 |
| 42 | .815 |
| 43 | .979 |
| 43.16 | 1 |

In particular the old sign-only onset at \(e^{3915}\) gives no
positive normalized margin there, whereas the new bounds have
margin at least 1 already at \(e^{43.16}\), on a connected ray.
At fixed earlier onsets, the following windows can beat the
full-ray margins (and do not claim a continuation of a constant
\(>1\) to infinity):
  
| closed log window | constant margin |
|---|---:|
| [37,39.47] | .21 |
| [37.2,39.47] | .29 |
| [37.3,39.47] | .33 |
| [38,39.47] | .57 |
| [39,39.47] | .82 |
| [45,65] | 1.18 |
| [46,60] | 1.24 |
| [48,59] | 1.28 |

The fixed-margin cuts .25, .50, .80 and 1 can thus be read directly
without confusing transient windows with ray guarantees. The margins
between 39.47 and 39.61 are covered by the .20 branch on
[39.47,39.7]; the loss of the sourced sign information is explicit.
The joins up to 49 use the preceding constant rows/cells; from
49 through 400 the first polynomial row below exceeds 1. From
400 onward the certified tail exceeds every constant in the ray table.

## Polynomial profiles

A coefficient list \([c_0,\ldots,c_k]\) means
\(\sum_{j=0}^k c_j/L^j\). Write \(M_j=\sum_{i=0}^{j}g_i/L^i\) for
the exact true Li coefficients in `orders.md`.

| inclusive log domain | coefficient list or expression |
|---|---|
| [49,infinity) | [1,13.69] |
| [55,145] | [1,14,115] |
| [55,175] | [1,14,40] |
| [62,106] | [1,14,145,1000] |
| [215,infinity) | [1,14,120] |
| [240,infinity) | [1,14,145,850] |
| [265,infinity) | [1,14,145,1412,7000] |
| [300,infinity) | [1,14,145,1412,13985] |
| [325,infinity) | [1,14,145,1412,13985,145450] |
| [400,infinity) | [1,14,145,1412,13985,145450,1500000] |
| [550,infinity) | \(M_{11}\) |
| [850,infinity) | \(M_{18}+15700000000000000000000/L^{19}\) |

Every ray beginning below 400 in this table is certified through 400
and dominated by the common analytic tail thereafter. The higher orders
from 550 and 850 have their own tail tests. Arbitrary fixed higher
order, with an explicit (usually later) computable onset, is proved in
`orders.md`. All these comparisons are proved inequalities, not
assertions that the envelope attains their suprema. They rely on
\(B_0\), and therefore are also valid with D01; the D01-specific
increment on matched domains is zero by `density.md`.
