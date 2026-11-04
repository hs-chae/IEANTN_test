# Explicit QRH comparison experiment

`StrongActualComparison` proves the actual normalized prime-counting bound
`Eπ(x) ≤ 0.009484 x^(-1/8)` and strict comparison with the explicit old
allowance functional for `exp(300) ≤ x ≤ exp(300.01)`.
The new bound itself holds for every `x ≥ exp(300)` in
`WinnerDensityA.HeightFinal.source_pi_009484`.

This package preserves the exact frozen source bytes of 72 comparison modules
and adds the separate `HalfWindow` and `HalfWindowRosser` legality providers. Flat module names are
intentional, so copied numerical certificates keep their precise declaration
and dependency identities. Existing modules are supplied by the named sibling
packages. `lake build WinnerComparisonA` builds the library with the canonical
Lean 4.34.0-rc2 toolchain; numerical native checks may take several minutes.

The old instance fixes a1=.611, a3=27.55, a2=6a1/e+a3, alpha=.11855,
delta=.3599 and d=.3663, retaining the original C4 integral, right moment,
boundary terms and Rosser window. Its source-derived moment upper theorem is
`WinnerOldC4Upper.actual_old_moment_at_T`.
The strict comparison concerns that declared functional and parameter witness,
not all old admissible parameters or the best possible bound.
`HalfWindow.high_closed_div_height` independently proves the reflected-pair
factor of two with actual multiplicities under finite-height RH.
`HalfWindowRosser.open_windowAllowance` then proves the exact old window
allowance for the actual strict count, from literal `OriginalSharpRosser` and
finite-height RH; the closed-count version is also proved.

The final theorem still takes the original analytic source statements,
verified finite-height RH and QRH as explicit inputs. The separate Lean 4.34.1
actual-OpenAI overlay supplies QRH; that overlay must not import these rc2
objects. The canonical joint comparison uses 89 audited finite native facts;
the new prime bound alone uses 49. This is native-assisted validation, not a
kernel-only claim, an official Comparator receipt or an assertion that all
analytic sources have been formalized from basic zeta theory.

Packaging manifests, source/object associations, inherited name-collision
resolutions, compiler receipts and the original proof-body audits are retained
outside this mathematical source package in the experiment evidence directory.
Private research notes and transcripts are not imported by this package.
