# Exact Fourier identity for the Gaussian witness

`GaussianActualFourier.lean` proves that the actual integral Fourier transform
of `GaussianKernel.physicalF` is `GaussianKernel.physicalG`. At an input x, each
function evaluates its unchanged rational coefficient list from
`gaussian_kernel/GaussianSources.lean` at √πx, then multiplies by exp(−πx²).
The Fourier convention is exp(−2π i x ξ).

The proof starts from Mathlib's Gaussian integral transform, proves the coordinate
multiplication rule by differentiating the Fourier integral, and extends it to
every rational Horner coefficient list. The even-coordinate rule is then reduced
to rational polynomial arithmetic. Existing `coeffAdd` and `coeffScale` are reused;
the derivative and trailing-zero normalization receive new correctness proofs.
The actual 25 output coefficients are computed and checked by Lean's kernel.

The final file also proves real and complex integrability, continuity, and evenness
of the actual functions. `GaussianFourierAudit.lean` checks the exact final types,
21 theorem axiom closures, and 16 actual proof-value edges. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. There is no Fourier-pair assumption,
new axiom, `sorry`, or native numerical execution axiom in these accepted proofs.
This is kernel mathematical verification, not source-first PV.

To rebuild these seven modules with fresh Fourier proof objects, run:

```sh
python3 reproduce.py --out /absolute/path/to/new-run
```

The default paths refer to the recorded research environment. Use `--context`,
`--gaussian-providers`, and `--lean-cert-providers` to provide its pinned generic
Lean/Mathlib context, the existing Gaussian numerical objects, and the inherited
LeanCert objects. The script snapshots all executed sources, records commands,
source/object identities, execution time and peak child RSS, and atomically writes
its receipt. It never imports an earlier Fourier application object.

The checked replay is `reproduction01`, with exact identity in `HANDOFF.json`.
This scoped replay explicitly reuses the numerical providers. A complete clean
reproduction must first rebuild the Gaussian numerical provider closure and then
run this script against those fresh objects; the combined campaign owns that run.
The numerical integral bounds belong to `gaussian_kernel`, and the RH prime-gap
consumer belongs to `gaussian_gap`. This directory proves neither by assumption
nor by renaming its Fourier identity a prime theorem.

Accepted proof sources, receipts and audits are retained. Failed development runs
remain separately recorded under the experiment-owned scratch path. The total
scratch footprint is small; no large regenerable arrays or datasets were created.
