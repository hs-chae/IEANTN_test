# Shared contracts: `Solutions/ProgramVerification`

A solution-facing Lake package. It is not a node, it is not in the core build, and no node
statement imports it. A provider's solution requires it by path, the same way solutions already
require `solution_FKS2Numerics_v2` for `SumStability`.

Its requirements are deliberately few: `IEANTN`, `solution_FKS2Numerics_v5` (which brings
`SumStability`, `FKS2Scalar`, `FKS2SumBridge` and `FKS2Table4.Rounding`) and
`solution_RamanujanNumerics_v1` (`ForwardRamanujan.Math`). Every requirement here enters every
provider's manifest, so application code stays out. This was learned the hard way: adding the
pilot here made `RamanujanNumerics.v3`'s manifest stale.

| Module | What it states | Axioms |
|---|---|---|
| `PVCore.Source` | the program shape, its renderer, the token scanner, `sourceMatches` | — |
| `PVCore.SumAffine` | operational `Exec`, the error theorems, the certificate `check` and its soundness `certified` | 3 standard |
| `PVCore.Bridge` | application bridges `le_bound_of_check`, `bound_le_of_check` | 3 standard |
| `PVRamanujan.Family` | the Ramanujan-budget family certificate and theorem, and the exact shift `budget_shift` | 3 standard |
| `PVCore.Kernel` | the kernel route: `decode`, `checkFrom`/`upperFrom`, `check_of_decode`, `upperCheck_of_decode` | 3 standard |
| `PVRamanujan.Kernel` | the kernel route for the family: `budgetFrom`, `budgetCheck_of_decode` | 3 standard |
| `PVCore.Chunked` | sums of more than 64 entries: `ChunkedProgram`, `ExecChunked`, `checkChunked`, `certifiedChunked`, `le_bound_of_checkChunked` | 3 standard |

## 1. The selected program

**Definition.** `PVCore.Program` has four fields:

```lean
structure Program where
  fnName : String
  inputs : List String               -- the static array's literals
  scale : String                     -- one multiplication
  ops : List (Sign × String)         -- then r = r ± c, in order
```

It has no field for an expected output or an accuracy.

**What it renders.** `render p` is the frozen `sum` function followed by

```c
static const double inputs[n] = {…};
double fnName(void) { double s = sum(inputs, n); double r = (s * scale); r = (r ± c₁); … return r; }
```

`sourceMatches src p` holds when the actual file has exactly this token stream. Comments and
preprocessor lines make the scan fail, so such a file never matches.

**Small example.** `⟨"f", ["0.5", "0.25"], "4.0", [(.minus, "1.0")]⟩` computes
`RN(RN(RN(0 + 0.5) + 0.25) · 4) − 1` in binary64, which is exactly `2`.

**Checked against reality.** One renderer reproduces all six existing selected files: Table 4 old
and QRH, Ramanujan old and updated, and both grouped variants. Two negative cases are rejected
(`pilots/pv-replay/tests/TokenMatch.lean`). The pilot's two files match through their
certificates.

## 2. Execution: a relation, not a claim

```lean
def Exec (src : String) (p : Program) (initial : CState) (out : ℚ) : Prop :=
  sourceMatches src p = true ∧ 1 ≤ p.inputs.length ∧ p.inputs.length ≤ 64 ∧
  ∃ xs s final, p.inputs.mapM loadLiteral = some xs ∧ RepresentsInput initial xs ∧
    runSum xs 0 = some s ∧ ExecC selectedSumProgram initial final s ∧
    runSuffix p s = some out ∧ SuffixIEEE p s out
```

- `loadLiteral s = (decimal s).bind round64`: a decimal literal as the binary64 value that
  round-to-nearest gives.
- `ExecC` is the frozen big-step semantics of the C loop (`SumStability.Source`). It covers the
  guard, the address load, the RN64 addition and the uint32 increment.
- `SuffixIEEE p s out` says each later operation is one IEEE round-to-nearest-even step:
  `RN64 (s · scale) r₀`, then `RN64 (rᵢ ± cᵢ) rᵢ₊₁`.

## 3. The error theorems

The exact value is `exactValue scale ops x = scale · x ± c₁ ± …`. Hypotheses:

- `1 ≤ n ≤ 64` entries, each a binary64 value in `[2⁻⁴⁰, 1]`;
- `0 ≤ scale`;
- `|q − exactValue scale ops s| ≤ eps` for the evaluated output `q`.

These are inherited from `SumStability`; this file does not generalize its rounding lemmas.

```lean
theorem exact_le_out … : exactValue scale os xs.sum ≤ out + forwardError scale s eps xs.length
theorem out_le_exact … : out - forwardErrorLower scale s eps xs.length ≤ exactValue scale os xs.sum
-- forwardError      scale s eps n = scale · (s / (1 − γ_{n−1}) − s) + eps
-- forwardErrorLower scale s eps n = scale · (s − s / (1 + γ_{n−1})) + eps
```

**How they are proved.** Both consume `SumStability.c_sum_forward_error`, the existing proved bound
`|ŝ − Σ xᵢ| ≤ γ_{n−1} Σ |xᵢ|` with `γ_k = k·u/(1 − k·u)` and `u = 2⁻⁵³`. They add the suffix
error. `gamma_lt_one` shows `γ_{n−1} < 1` for `n ≤ 64`.

## 4. One certificate per instance, with a soundness proof

`check src p eps : Bool` evaluates the instance and checks the following:

- the token match;
- the length;
- every input is a binary64 value in `[2⁻⁴⁰, 1]`;
- every loop addition and every suffix step rounds correctly (`FKS2Table4.additionCheck`);
- `0 ≤ scale`;
- `|out − exactValue(s)| ≤ eps`.

**Fails closed.** `additionCheck` covers only positive normal results with exponent in
`[−100, 100]`. Any other intermediate makes `check` return `false`.

```lean
theorem certified (h : check src p eps = true) :
    let v := valuesOf p
    Exec src p (initialFor v.xs) v.out ∧ ValidInputs v.xs ∧ (1 ≤ v.xs.length ∧ v.xs.length ≤ 64) ∧
    0 ≤ v.scale ∧ exactValue v.scale v.ops v.xs.sum ≤ v.out + forwardError … ∧
    v.out - forwardErrorLower … ≤ exactValue v.scale v.ops v.xs.sum
```

`certified` is a kernel-checked theorem. The only native step in an instance is evaluating its own
`check` (`native_decide`). That evaluation is what the local gate records and audits. `certified`
also yields a **concrete execution witness**: `Exec` of the actual file with the evaluated output,
not a conditional statement.

## 5. Application bridge

An application proves, with its own mathematics, that its quantity `T` is at most what the
program computes in exact arithmetic:

```lean
theorem le_bound_of_check (h : upperCheck src p eps bound = true) {T : ℝ}
    (hT : T ≤ (valuesOf p).scale * (valuesOf p).xs.sum + opsConst (valuesOf p).ops) : T ≤ bound
theorem bound_le_of_check (h : lowerCheck src p eps bound = true) {T : ℝ}
    (hT : (valuesOf p).scale * (valuesOf p).xs.sum + opsConst (valuesOf p).ops ≤ T) : bound ≤ T
```

`upperCheck` is `check` plus `out + forwardError ≤ bound`.

## 6. The Ramanujan-budget family

```lean
def budgetCheck (src) (p) (m M A Y eps bound : ℚ) : Bool  -- check + ops = [−134, −max 0 m]
                                                          -- + Σ termsQ m M A Y ≤ scale·Σ x + 0 ≤ M + 0 < Y + out+err ≤ bound
theorem budget_of_check (h : budgetCheck src p m M A Y eps bound = true) :
    ∀ x > exp Y, εUpper M x − εLower m (exp A) x ≤ bound
```

`termsQ` is `ForwardRamanujan.terms` in rationals (`termsQ_sum_cast`). The step from the program
to the inequality is `ForwardRamanujan.epsilon_majorant`, reused unchanged.

## 7. Where the shared proof is actually used

| Proof path | Shared theorems in its closure | Instance code (code lines) | Native facts, before → after |
|---|---|---|---|
| `RamanujanNumerics.v1` replay | `certified`, `budget_of_check` | 11 | 6 → 1 |
| `RamanujanNumerics.v2` replay | same | 10 | 6 → 1 |
| grouped variants (1 entry) | same | 12, 13 | 6 → 1 each |
| **`RamanujanNumerics.v3` (new provider)** | same | 26, generated | — → 1 |
| `FKS2Numerics.v7` replay (Table 4 QRH) | `certified`, `le_bound_of_check` | 27 | 8 → 4 (3 analytic facts kept) |
| `FKS2Numerics.v6` replay (Table 4 old) | same | 25 | 8 → 4 (3 analytic facts kept) |
| pilot chain, stage A and stage B′ | `le_bound_of_check`, `budget_of_check` | 64 for the whole chain, including its analytic glue | 13 → 2 |

**What "reused" means here.** The same proved theorems are applied, not the same interface
restated. The 116-line Ramanujan instance file carried 18 theorems; an instance now has 2, its
certificate and its statement. The 382 shared code lines are written once:

- PVCore: 335;
- Ramanujan family: 47.

**What did not get shorter.** Table 4's analytic enclosures, of the cells, the anchor, the point
and the tail, are mathematics and stay with the application. They are reused as they are, with
their 3 native facts.

## 8. Exact shift, for negative budgets

```lean
theorem budget_shift (hm : 0 ≤ m) (h : εUpper M x − εLower 0 xa x ≤ C) :
    εUpper M x − εLower m xa x ≤ C − m
```

`εLower m = 206 + m + …` for `m ≥ 0`. When the true budget is negative, the program's last
intermediate would be negative, and the shared rounding certificate covers positive normal values
only. The program runs at `m = 0` and the proof subtracts `m` exactly. Used by the two-backend
chain (budget `−7.72`).

## 9. Kernel route: one native fact, for decoding

`check` is one Boolean computation; an instance proves it with one `native_decide`, so the
compiled evaluator runs all of it. The kernel can reduce almost all of it itself. Only decoding
the decimal literals cannot be reduced: `FKS2Scalar.decimal` uses `String.splitOn` and
`String.toNat?`.

```lean
def decode (p : Program) : Option (List ℚ × ℚ × List (Sign × ℚ))       -- parsing only
def checkFrom (src p eps xs scale ops) : Bool                           -- check, on given rationals
theorem check_of_decode (hd : decode p = some (xs, scale, ops))
    (hk : checkFrom src p eps xs scale ops = true) : check src p eps = true
```

`upperFrom`/`upperCheck_of_decode` and `budgetFrom`/`budgetCheck_of_decode` do the same for the
upper-bound bridge and the Ramanujan family; the latter also return the decoded fields of
`valuesOf p`. `certified` and the family theorems then apply unchanged. Measured on the A→B′
chain: 2 native facts, both `decode … = some …`; 177 s and 22.7 GB to build the module.

## 10. Chunked sums: more than 64 entries

The proved loop bound covers one call of the frozen `sum` over 1–64 entries. A longer sum is
written as several calls whose results the wrapper adds:

```c
double s = sum(inputs0, n0); s = (s + sum(inputs1, n1)); …; double r = (s * scale); r = (r ± c); …
```

- **Semantics.** `ExecChunked`: each chunk is an execution of the frozen loop on its own array
  (`ChunkRun`, with `SumStability.ExecC`), each wrapper addition one binary64 rounding
  (`CombineIEEE`), then the usual suffix.
- **Error bound.** No new analysis: the exact total is at most `Σⱼ sⱼ/(1 − γ_{nⱼ−1})` and at least
  `Σⱼ sⱼ/(1 + γ_{nⱼ−1})` (the per-chunk loop theorem, summed), and the wrapper's roundings enter
  through the computed total itself, because every value is concrete.
- **Certificate.** `checkChunked`: token match of the actual file, each chunk's length and input
  domain and rounding chain, each wrapper addition, the suffix, and `|out − exact(total)| ≤ eps`.
  `certifiedChunked` gives `ExecChunked` and both bounds; `le_bound_of_checkChunked` is the
  application bridge.
- **Used by** Table 4 QRH in two chunks of 15 (same statement `FKS2Numerics.v7.qrh_pi`) and a
  100-entry contract test (`pilots/pv-replay/PVReplay/Chunked.lean`).

