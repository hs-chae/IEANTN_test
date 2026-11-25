# Physical56 Fourier proof from the preserved opt28 input

The actual Mathlib Fourier transform of `RH080.Gaussian28.physicalF` equals
`physicalG`, with the convention exp(−2πixξ). Both functions are continuous,
even and integrable. The proof consumes exact kernel identities from all29
preserved original monomial coefficients through the Laguerre28 recurrence to
all57 physical polynomial positions; no old actual witness is used.

`python -OO reproduce.py --out /fresh/output` rebuilds32 application and
LeanCert modules using only pinned Mathlib caches. The checked final replay
took106.56 seconds, with17 theorem roots,10 direct proof edges and only
`propext`, `Classical.choice`, `Quot.sound`. Nine actual CLI/type controls
passed, including normal/-O/-OO rejection checks. See `evidence/`.

This additive proof preserves the original trial inputs and outcomes. It is
kernel verification, not source-first PV. The full numerical/CMS closure and
its separate cold replay are in `../primal56_gap/`.
