# Work and verification notes

- Read the bound contract, foundations, baselines, checkpoint/operating
  rules, budget, runtime paths and source index. Used no outside source,
  delegate or network. Early candidate, 75% snapshot, and prior locks were
  retained (snapshots outside the final flat directory).
- The main elementary Ramanujan transfer used two-sided finite asymptotic
  sums with a differential residual and derivative-checked interval meshes.
  A CH2 constant plateau alone cannot fill the large gap; it stops near
  log x=754. Log-convexity applies to positive zero sums at a common cutoff,
  not to the signed prime-counting error. The FKS interpolation therefore
  used common zeros and a reliable alternate truncation formula.
- The simple QRH reciprocal-sum route gave a full real ray, but wasted
  logarithmic factors; the right-hand density tail is convergent, allowing
  their removal. The first 128-cell upper certificate missed the .270 cap
  at 169; increasing to 256 and replacing repeated arithmetic by
  outward dyadic boxes resolved it. Tested extra smooth margins at lower
  onsets; the (weaker) pure shifted-envelope proof missed 144 at 233,
  corrected to 239 for that auxiliary route.
- Initial Mertens experiments used floating point for candidate selection
  only. The loose exp(z)-1 <= z/(1-z) approximation missed the near-optimal
  product onset. A quadratic enclosure and a sharp tail for the prime
  constants fixed that. A proposed .09 weighted coefficient from 24M
  fails the interval check near 30.67M; moved to 35M. A coarse tail for
  B3 failed the high-precision enclosure test and was replaced by the
  proved theta-tail method. Final integer sweep output: left witnesses
  passed at 912559.997, 2278381.710 and 2278382.112; final endpoint and
  constant closure passed at 268435456. Scaled endpoint check counts:
  28925578, 28925574, 29117294 (products, reciprocals, weighted).
- No rerun of CH2's original 10^13 computation, finite RH, FKS source
  tables, Ramaré source proof or the large historical small-x Ramanujan
  computation. New local Ramanujan counts (and the last real root) and
  the finite Mertens table are independently reproduced, not asserted
  from the original rounded data. FKS Remark 3.3's potential problem
  with its earlier explicit formula is sidestepped by its stated
  Theorem 3.2, not by an independent validation of Table 5.
- No primorial sign/Nicolas-type inequality is claimed: the signed
  remaining integral is not controlled in sign by these assumptions.
  The exact boundary exponents 27/32 and 7/8 allow zeros on the boundary.
  No proof of a strictly better exponent is given.
