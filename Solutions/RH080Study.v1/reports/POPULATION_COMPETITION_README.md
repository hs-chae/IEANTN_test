# Three stated population-width formulas

This additive figure compares the G56 limiting population coefficient, the 2026 paper's two-line population envelope for modulus 1, and the preserved explicit octic coefficient. It leaves the original figure and all 278 mandatory mathematical inputs unchanged.

The smallest of these three formulas is G56 until α ≈ 0.106017430; the paper's first line until α ≈ 0.202333898; its second line until α ≈ 0.454117642; and the octic formula thereafter. The old G56/octic crossing at α ≈ 0.349929069 is **not** a switch of this minimum: the paper's formula is strictly smaller there. Exact rational coefficients, crossings and all plotted rows are in COMPETITION_FRONTIER.json and COMPETITION_FRONTIER.csv.

The paper input is Theorem 2, equation (ap-weighted), in version 2 (21 November 2026), DOI https://doi.org/10.5281/zenodo.24429650. Section 3's “The moduli 1 and 2” remark justifies the ordinary RH specialization. Its bound is eventual, with no explicit numerical onset supplied by this population theorem. The manuscript PDF SHA-256 is 2f15da8545766012902e6dcc46f9bc4daa9951661dae2cc4809b97fd729dc380; the supplement TeX SHA-256 is 3c05af131a1603bd9af2df87a44bb20a651220b454015faf7412896e3cbb92b2.

G56 has its existing RH/general CMS source assumptions, eventual onset and a positive epsilon allowance. The octic curve keeps its existing explicit-formula/RH input package and onset x ≥ exp(24). The graph compares their stated scalar coefficients; it does not prove a new ANT transfer, identical hypotheses/onsets, a globally best envelope, or optimality.

PopulationCompetitionComparison.lean proves the exact crossing order, all four continuous minimum regions, continuity, and the paper's strict superiority at the old crossing. All 11 audited roots use only propext, Classical.choice and Quot.sound. This is a kernel-only scalar proof, **not source-first PV**. It supplies no new prime-counting theorem.

From a checkout or extracted bundle with the pinned generic context prepared by the main REPRODUCE.md:

```sh
python3 Solutions/RH080Study.v1/reports/reproduce_competition_scalar.py --context /fresh/context.json --run /fresh/competition-scalar
```

The context must name exactly the eight pinned generic libraries, Lean 4.34.0-rc2 and compiler hash required by the script. No application objects are accepted as inputs. Prepare the figure renderer with Python 3.11 and Matplotlib 3.10.7 (its transitive dependencies are ordinary rendering infrastructure), then run:

```sh
python3 Solutions/RH080Study.v1/reports/plot_population_competition.py --render-package /fresh/render-packages --out /fresh/competition-figure
python3 Solutions/RH080Study.v1/reports/test_competition.py --context /fresh/context.json --render-package /fresh/render-packages --run /fresh/competition-controls
```

Both output directories must be fresh. The plotter renders fonts to paths in standalone SVG/PDF; exact arithmetic is in CSV/JSON and Lean. The control script actually runs the scalar compiler and figure generator in normal, -O and -OO modes, rejects 15 malformed/reuse cases and checks byte-identical figures. Receipts are under population-competition-evidence/. No heavy ANT proof is rerun for this auxiliary figure.
