# Round 3: QRH-driven evolution of the Table 4 θ→π transport

Project: `Solutions/Table4Evolution.v1` (solution-local). Generator: `scripts/generate.py` (untrusted;
Lean re-checks every literal). All numbers below are re-derivable with
`python3 Solutions/Table4Evolution.v1/scripts/generate.py` and the Lean build.

## 1. The mathematics being executed

For `x ≥ e^330`, partial summation from `e^300` gives (`FKS2Pair.whole_ray_transport`, generalized
here to `Table4Evolution.whole_ray`)

```
Eπ(x) ≤ (330/300)·e^{-30}·(a + U(300))                      anchor, a = Eπ(e^300) ≤ 1.6997·10⁻¹²
      + Σ_cells 330·e^{-330}·u_cell·(e^{hi} − e^{lo})/lo²   the finite part ∫_{e^300}^{e^330}
      + U(330) + U(330)/328                                 the point x and the ray beyond e^330
```

where a cell `[lo, hi]` carries a whole-tail θ allowance `u_cell` valid on `[e^{lo}, ∞)`. Round 1–2
programs fixed the 30 unit cells `[300+j, 301+j]`. Here the partition is data.

**Input profiles (the θ side).**

| profile | `U(L)` on `L ≥ 300` | source | at `L = 300` | at `L = 330` |
|---|---|---|---|---|
| QRH-free (FKS2 Table 3) | `1.6930, 1.6882, 1.6837, 1.6795 ·10⁻¹²` from `L = 300, 310, 320, 330` (whole-tail steps, no interpolation) | `FKS2.v8.table3_theta_*` | `1.6930·10⁻¹²` | `1.6795·10⁻¹²` |
| QRH, `Q(L) = L²/283·e^{-L/8}` | continuous | `QRHCH2.v5.psi_refined_bound` via `FKS2Table4.theta_input` | `1.67·10⁻¹⁴` | `4.684·10⁻¹⁶` |
| Agent A, `K·e^{-L/8}`, `K = 0.009782 + 10⁻¹²` | continuous | `WinnerDensityA.revers_source_theta300` (hypothesis here) | `5.1·10⁻¹⁹` | `1.19·10⁻²⁰` |
| Agent A, `K = 0.009904 + 10⁻¹²` | continuous | `WinnerDensityA.source_theta300` (hypothesis here) | `5.2·10⁻¹⁹` | `1.21·10⁻²⁰` |

Under QRH the cell values `330·e^{-330}·Q(lo)·(e^{hi}−e^{lo})/lo² = (330/283)·(e^{hi−lo/8−330} − e^{7lo/8−330})` decay geometrically
toward `L = 300` (ratio `e^{-7/8}` per unit); under the step profile the ratio is `≈ e^{-1}`. In both
cases the weight `e^{b−330}` makes the cells far from 330 negligible, and the point term `U(330)`
dominates: 99.3% of the QRH allowance, 99.4% of the QRH-free one.

## 2. The executed program

Every configuration is the same restricted-C shape, the shared contract `PVCore.Program`: the
frozen `sum` loop over the cell literals, one multiplication by the scale `2^{-k}`, three additions
(anchor, point, tail). The frozen loop is byte-identical to round 1. Cell literals are upward
binary64 roundings of `2^k·cellHi`, where `cellHi` is the exact rational upper bound
`(330·m/lo²)·(expHi(a)⁴ − expLo(b)⁴)` (`Table4Evolution.cellHi`, exponential enclosures by an exact
18-term Taylor polynomial at a quarter of the exponent). `k` is chosen so that every literal lies in
`sum`'s proved input range `[2^-40, 1]`.

Two-cell QRH program (`c/qrh_trunc2.c`, sha256 `ef750c59…`):

```c
/* the frozen `sum` (round 1, byte-identical), then: */
static const double inputs[2] = {
    0.7999073965026894939001067541539669036865234375,
    0.036628287383099832064115020102690323255956172943115234375
};
double fks2_table4_transport(void) {
    double s = sum(inputs, 2);
    double r = (s * 0.0000000000000000277555756156289135105907917022705078125);    /* 2^-55 */
    r = (r + 0.00000000000000000000000017665089669250357659020871109627738508254054851897432852679253658940809745825362142568337731063365936279296875);
    r = (r + 0.0000000000000004683753925250112014211433790943236597355769056105767589315291843377053737640380859375);
    r = (r + 0.000000000000000001427973757698204816618073176699030809477512038595703632026800988796821911819279193878173828125);
    return r;
}
```

The first literal is `2^55·cellHi` of the coarse cell `[300, 329]` (allowance `Q(300)`), the second
of `[329, 330]` (allowance `Q(329)`). The three constants are the anchor, `Q(330)` and `Q(330)/328`,
the same literals as `FKS2Numerics.v5`. (The `/* … */` comments are added here; the file has none, since a comment would fail the token check.)

## 3. Ablation: what changed the bound, what changed the work

Exact allowances (mpmath, 40 digits) and program outputs; the registered targets are
`5·10⁻¹⁶` (QRH) and `1.69·10⁻¹²` (QRH-free).

| input | program | cells | literals | exp. certificates | allowance | registered target | native facts | Lean module build |
|---|---|---|---|---|---|---|---|---|
| QRH-free | old (FKS2Numerics.v6) | 30 | 30 | 31 | `1.68977·10⁻¹²` | met | 4 (`PVTable4.Old`) | — |
| QRH | old (FKS2Numerics.v5/v7) | 30 | 30 | 34 | `4.7155·10⁻¹⁶` | met | 4 (`PVTable4.QRH`) | — |
| **QRH** | **evolved: 2 cells** | **2** | 2 | 7 | `4.9302·10⁻¹⁶` | **met** | **1**; **0** kernel route | 5 s; kernel 147 s, 27.8 GB |
| QRH-free | **evolved: 3 cells** (control) | 3 | 3 | 7 | `1.68991·10⁻¹²` | **met** | 1 | 5 s |
| QRH | refined: 120 quarter cells (chunked 64 + 56) | 120 | 120 | 243 | `4.7145·10⁻¹⁶` | met, `−0.02%` | 1 | 5 s |
| Agent A `0.009782` | evolved: 4 cells | 4 | 4 | 11 | `1.2077·10⁻²⁰` | (new statement) | 1 | 5 s |
| Agent A `0.009904` | evolved: 4 cells | 4 | 4 | 11 | `1.2227·10⁻²⁰` | (new statement) | 1 | 5 s |

Minimal number of explicit unit cells next to 330 (plus one coarse cell from 300) that still meets
the registered target, from the exact allowances:

| explicit cells `k` | 0 | 1 | 2 | 3 | 5 | 30 (uniform) |
|---|---|---|---|---|---|---|
| QRH allowance | `5.30·10⁻¹⁶` ✗ | `4.93·10⁻¹⁶` ✓ | `4.79·10⁻¹⁶` | `4.74·10⁻¹⁶` | `4.72·10⁻¹⁶` | `4.715·10⁻¹⁶` |
| QRH-free allowance | `1.69083·10⁻¹²` ✗ | `1.69015·10⁻¹²` ✗ | `1.68991·10⁻¹²` ✓ | `1.68982·10⁻¹²` | `1.68978·10⁻¹²` | `1.68977·10⁻¹²` |

**What truly improved.**

1. **Input change, unchanged program** (QRH-free → QRH, 30 cells): the bound improves about 3,600-fold,
   `1.69·10⁻¹²` → `4.715·10⁻¹⁶`. All of it is the θ input.
2. **Program change, same input** (30 cells → 2 cells, QRH): 15× fewer cells, 5× fewer exponential
   certificates, one native fact instead of four, and a kernel-only proof becomes affordable. The
   bound gets **worse** by 4.6% and stays below the target. Faster, not stronger.
3. **The same program change under the QRH-free input** (30 → 3 cells): it also works. **The
   truncation is not driven by QRH**; QRH saves one cell because its allowance has 6% slack below its
   target against the QRH-free 0.01%.
4. **QRH-specific refinement** (120 quarter cells): possible only because `Q` is defined for every
   real `L`; a step profile gains nothing below its steps. It buys `0.02%`: no partition of
   `[300, 330]` can move the point term `U(330)`.
5. **A later profile, unchanged proof core**: Agent A's θ coefficient through 4 cells gives
   `1.2078·10⁻²⁰`, four orders of magnitude below the registered QRH target, a second route to a
   bound Agent A already has (`1.153·10⁻²⁰`).

## 4. The consumer

Every configuration ends in the same generic theorem, `Table4Evolution.pi_bound`:

```lean
theorem pi_bound {s : ℚ} {k : ℕ} {mOf : ℚ → ℚ} {rest xs : List ℚ} {a p t B : ℚ}
    (hprof : ProfileOK s mOf) (hAnchor : FKS2.v6.table4_anchor_300)
    (hcells : cellsOK s k mOf (300 :: rest) xs = true)
    (hlast : (300 :: rest).getLast (List.cons_ne_nil _ _) = 330)
    (hconst : constOK s (mOf 300) (mOf 330) a p t = true)
    (hB : ((1 / 2 ^ k : ℚ) : ℝ) * (xs.sum : ℝ) + ((a + p + t : ℚ) : ℝ) ≤ B) :
    HasNumericalBound Eπ B (exp 330)
```

`hB` comes from the program certificate (`PVCore.le_bound_of_check` or `le_bound_of_checkChunked`);
`hcells`, `hlast`, `hconst` are finite checks; `hprof` is the only analytic input.

## 5. Changed-input replay and rebuild scope

`agentB/evidence/rebuild_scope.sh` (log `pv5/rebuild_scope.log`). Changing `K` of the Agent A
configuration from `0.009782` to `0.009904` and regenerating changes the C file
(`80b73a58… → 09aa4ec3…`) and the data module (`476db705… → 1b702e42…`). Then:

- `lake build` with the **old statement** (`Eπ ≤ 1.2078·10⁻²⁰`) rebuilds exactly
  `Table4Evolution.AgentATrunc` among the proof modules (plus the 1-second data modules) and
  **fails**: the certificate is false for the new input;
- restating `K` and the bound (`Eπ ≤ 1.2228·10⁻²⁰`) rebuilds the same module and passes;
- editing one digit of a literal in the C file only rebuilds the same module and fails (source
  mismatch).

**Lake finding.** A module built through another library's import was traced without its own
library's `needs`: building the umbrella module after a C edit replayed the stale certificate, while
building the configuration's library rebuilt it. The default targets are therefore the five
configuration libraries; the umbrella library lists every C file (coarse, never stale).
