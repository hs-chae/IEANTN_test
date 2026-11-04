# Winner program v2: actual prime-error consumers

Start with `Solution.lean`. This isolated source package proves actual IEANTN normalized prime-error bounds, conditional on precisely named upstream mathematical statements. This is local native-assisted evidence, not an official IEANTN receipt.

| Endpoint | Critical-line source/configuration | Bound for all x >= exp(300) |
|---|---|---|
| `WinnerDensityA.HeightFinal.source_pi_009484` | Four certified height profiles + direct pi kernel, Revers .611 | E_pi(x) <= .009484 x^(-1/8) |
| `WinnerDensityA.source_pi300` | HPY .618, first Gaussian enclosure | E_pi(x) <= .009952 x^(-1/8) |
| `WinnerDensityA.tight_source_pi300` | Same HPY input, tighter accepted enclosure | E_pi(x) <= .009898 x^(-1/8) |
| `WinnerDensityA.revers_source_pi300` | Revers .611, recomputed amplitude/kernel/certificate | E_pi(x) <= .009830 x^(-1/8) |

`E_pi(x)=abs(pi(x)-Li_2(x))/(x/log(x))`, with the offset logarithmic integral from 2. Thus the strongest bound means `abs(pi(x)-Li_2(x)) <= .009484*x^(7/8)/log(x)`. Start at `winner_program_v2_height` in `Solution.lean`; the older endpoints are preserved controls.

The proof derives the improved actual zero count from original mollifier/mean-square/smoothing/interpolation/Littlewood relations; it does not assume a new density or prime-error bound. `SourceContext.OriginalInputs` and `ReversContext.ReversInputs` list the eight upstream source leaves literally on actual zeta, finite Mobius mollifier and integral objects. Their Littlewood relation requires finite RH and holds outside a countable exceptional set. `ExceptionalDensity.zetaN_extend` proves the new continuous density majorant at every height. The original low-height error, all truncation terms, prime powers and partial summation are included.

The three older endpoints also take the thirteen unchanged `CH2Source` statements, finite RH through 3e12, and QRH with boundary7/8. The separate compatible actual-QRH overlay supplies the pinned OpenAI theorem in Lean4.34.1; canonical source builds use Lean4.34.0-rc2. The eight original source leaves and CH2/finiteRH inputs are still explicit, not claimed fully supplied.

The strongest endpoint takes the literal original signed CHJ explicit formula, three Riemann-von Mangoldt/low-zero source statements, the eight-field `WinnerNewHeightSource.PrimaryInputs`, finite RH through 3e12, and QRH7/8. It does not require the other unused CH2 bundle fields. `HeightPrimary`, `HeightMoment`, `StepMoment`, `HeightSpectral` and `HeightResult` derive the full chain. The same finite RH input is used at all four arithmetic anchors; higher anchors do not assert additional RH verification.

`HeightProgram.program 300 100 8192` evaluates the actual two-row spectral enclosure. `HeightCertificate.checked` is its concrete accepted native execution. `HeightSharpCertificate` derives the exact upper coefficient .009474448; the direct pi consumer gives .009483932448, rounded to .009484. Generic analytic and semantic reductions use the standard three axioms; concrete numerical instantiations carry their disclosed finite checks. The final bound has49 explicitly audited finite native facts, and the separate joint comparison has89. Original source assumptions remain distinguishable from these new proofs.

`ModelProgram.program` generates the exact dyadic interval calculation. Its proved denotation is the actual sigma-grid coefficient, and `SharpCertificate`, `TightCertificate` and `ReversCertificate` supply concrete accepted executions. The original Gaussian integrals, both tails, source scalar caps, and full-range count extension are in `../WinnerSourcesA.v1`; the four new height-specific Gaussian enclosures and scalars are in `../WinnerHeightSourcesA.v1`; the actual mollifier normalization and source bridges are in `../WinnerBetaA.v1`.

CLI source `HeightMain.lean` exposes `height300` with both actual interval rows and their domain flags. `Main.lean`, `TightMain.lean`, `ReversMain.lean` retain four/two/two active finite computation routes respectively; unknown or missing routes return2. No binary64 arithmetic is claimed. See the delivered evidence scripts for pinned cache-aware rebuilds and explicit runtime checks.

The mathematical construction improves an explicit instantiation of an existing source family. It does not establish optimality or a global best-known envelope. The exact raw Minkowski family contains our finite enclosure; broader unresolved competitors must remain visible. Read `reports/WINNER_V2_RESULT.html` in the delivered bundle for the final comparison and gate status.
