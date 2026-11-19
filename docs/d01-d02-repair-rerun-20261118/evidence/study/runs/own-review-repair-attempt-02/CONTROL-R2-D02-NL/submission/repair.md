# Planned own-review repair of FOLLOWUP-C017

Canonical stage CONTROL-R2-D02-NL; exact same hypotheses and same
logical mathematical stage. This is not a fresh baseline run.
The own review was read from the packet names in OWN_REVIEW_INDEX.json
and checked against their indexed hashes. No other arm, unmounted
referent of any indexed path, or new literature was used.

## Disposition

* **R-regularity (the only rejected prior mathematical item):**
  withdrawn as stated. The old R2 formula is a piecewise
  real-variable lower profile, not continuous. In our own recomputation
  the left-minus-right remainder jump at L=32 is strictly between
  6.8283e-12 and 6.8284e-12 (repair_joins_run.txt). In both local
  arguments 32 and 31 the active finite pi minima are continuous:
  no source guard crosses a domain boundary there. The upper
  normalized pi bracket is positive, so a nonzero remainder jump
  gives a nonzero jump in the negative square, rather than a bound
  failure. The old inequalities are unchanged; they require no
  continuity. There is now a separate genuinely continuous spectral
  lower profile on L>=141, with fixed anchor and no finite-source
  switches (repair_applications.md).
* **FKS locator:** actual PDF page 2 for Theorems 1.1, 1.2 and
  Corollary 1.4, corrected in sources.md. No domain or formula changed.
* **Early Ramanujan source domain:** keep the concrete counterexample
  to the printed real endpoint, not to the terminal sign theorem
  proved here. The integer finite range up through the needed join
  is still inherited at literature trust, not a fresh execution of
  the historical algorithm; no RH premise or unverifiable assertion
  about its real stepping proof is used. Our local exact count,
  endpoint bracket, and analytic tail remain available.
* **Numerical and comparison scope:** the prior numerical evidence
  remains at ordinary interval/sieve and original-literature trust.
  The formulas describing a B0-certificate obstruction do not
  assert lower bounds on arithmetic errors. All common originals
  remain available, in particular both QRH and verified finite RH.
  No result is attributed to the hypothetical assumption merely
  because it improves an older inverse-log bound.

The 451-row exact prior assessment is preserved in
prior_review_inventory.json (277 supported at stated trust, 172
baseline-retained, one equivalent/weaker, one false regularity item).
Its historical locators and statuses refer to the **original** bytes,
all 28 of which are preserved in prior_candidate.zip at original
filenames with hashes in OWN_REVIEW_INDEX.json. The archive deliberately
retains the false historical wording. The operative regularity
statement is in the amended live ramanujan.md. The original 450
unrejected items remain available, including the dominated raw transfer
and the finite-only prior certificates; some are strengthened by the
additive new proofs. The own assessment supplied no premise for
those new proofs.

## Substantive work after the assessment

* Kept the full density logarithmic power in height instead of
  exponential linearization; integrated signed Taylor bounds by
  moments. Convexity in the real-part parameter justifies the secant
  layer. An initial fixed-window implementation clipped interval
  nodes directly and hit a coefficient assertion. Even exact
  endpoint clipping can miss a transition panel: the corrected
  proof assigns the whole transition panel the full count bound.
  Very early attempts around u=166 using the new fixed-width menu
  still had uncertainty >1.07e-12; the proof of strict **envelope**
  dominance starts at 166.4, not at those unchecked smaller logs.
  Two endpoint-only optimizations with differing widths would not
  prove a bridge; the actual bridge holds a width fixed on each slab.
* For Ramanujan, used compact subslabs at each old early onset, and
  a distinct order-64 tail anchor with all coefficients screened.
  The first provisional 2*10^6 residual allowance at 128 failed;
  the actual enclosure is in (56636640,56636745), so the repaired
  allowance is 6*10^7. Improvements to early margins are B0, and
  the D02 cap creates genuine fixed-margin and fixed-onset gains
  in the higher orders. The exact sign threshold is already B0.
* For finite Mertens arithmetic, replaced an expensive event-by-event
  extension with monotone raw prefix enclosures on whole blocks,
  and moved the analytic join from 25 to 60 million. This removed
  the old .10 and weighted .11 joining obstacles. The smaller
  coefficient .082 has a certified join; .08 for the weighted sum
  does not yet follow at the same join from the simple analytic bound
  (.0813419194... there). The next concrete options are a longer
  block sweep with later analytic join or an explicit sharper signed
  prime-power upper bound. Nothing about failure of the .08
  arithmetic inequality is claimed.
* The spectral decay powers still reflect the rightmost allowed
  zeros and their absolute density-weight sum. No cancellation of
  their phases is available from this proof, and the added premise
  does not rule out boundary zeros. A better power on this route
  would need stronger spectral information; a refined density upper
  bound or better smoothing could still lower constants. The
  repaired portfolio is not claimed globally optimal.

## Accounting and replay

The controller-indexed prior research generated-token lower bound is
105443; review tokens are excluded. This repair comprises the actual
operations described above, the new source and receipts. Cumulative
research is the prior controller lower bound plus the controller's
measurement of this repair, not a reset. No authoritative repair
token counter is exposed in the executor; no numerical cumulative
value beyond that prior lower bound is fabricated. The original
review replay is not counted as research work in the repair.

The initial non-login shell command printed the correct directory
and failed on ls (exit 127, command not found). Python file reads
and shell expansion recovered access immediately. The C.UTF-8
locale warning did not impede any proof or replay. All fourteen
permitted PDF/text objects were hashed, and the bound page-marked
originals were used for locators. The extraction-based review and
ordinary interval checks are not Lean or source-first PV.

Reproduce the added evidence in this directory using non-login
/bin/bash and /usr/bin/python3.10 -B:
```
repair_finite.py      -> repair_finite_run.txt
repair_spectral.py    -> repair_spectral_run.txt
repair_r.py           -> repair_r_full_run.txt
repair_joins.py       -> repair_joins_run.txt
repair_portfolio.py   -> repair_portfolio.json
repair_evaluate.py log 200 -> repair_eval_run.txt
```
The finite extension is the slow step. The two fine sweeps are not
confused: repair_finite.py uses the already certified original
normalizer intervals from finite_run.txt, but independently sieves
and bounds the new entire interval. The original certificates
remain separately executable as in candidate.md and restart.md.
