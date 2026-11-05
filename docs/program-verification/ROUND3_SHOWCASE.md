# Verified numerics in IEANTN: one program, three roles

For a reader who knows the analytic number theory and not program verification. Every claim here is
a Lean theorem that was compiled and whose axioms were printed; the names are given so it can be
checked.

> **Speaker notes (한국어).** 이 문서는 프로그램 검증을 모르는 수학자를 위한 것이다. 수학 입력(QRH), 수치 프로그램 검증, 프로그램 진화를 구분해서 보여준다. 모든 주장은 컴파일된 Lean 정리이고 공리를 확인했다.

## 1. Three roles, kept apart

| Role | What it is | Example here |
|---|---|---|
| **Mathematical input (QRH)** | A hypothesis about ζ: no zeros with `Re s > 7/8`. It never runs; it enters as the premise of a theorem. | `Eθ(x) ≤ Q(log x)` with `Q(L) = L²/283·e^{-L/8}`, from `QRHCH2.v5.psi_refined_bound` |
| **Program verification** | A proof that a specific C file, read by Lean from disk, computes an upper bound of a specific real number, rounding included. | the transport program below proves `Eπ ≤ 5·10⁻¹⁶` on `x ≥ e^330` |
| **Program evolution** | Changing the program itself (not only its constants) when the input changes, under the same correctness theorem. | 30 cells → 2 cells |

> **노트.** QRH는 실행되지 않는 가정이다. 프로그램 검증은 디스크의 C 파일이 어떤 실수의 상계를 계산한다는 증명이다. 프로그램 진화는 입력이 바뀔 때 상수가 아니라 프로그램 자체를 바꾸는 것이다.

## 2. The mathematics being computed

For `x ≥ e^330`, partial summation from `e^300` bounds the normalized error
`Eπ(x) = |π(x) − Li(x)|/(x/log x)` by

```
anchor  +  Σ over cells [lo, hi] of 330·e^{-330}·U(lo)·(e^{hi} − e^{lo})/lo²  +  U(330)  +  U(330)/328
```

where `U` is a whole-tail bound for `Eθ` and the anchor uses `Eπ(e^300) ≤ 1.6997·10⁻¹²`. The cells
cut `[300, 330]` (in `log x`); the program adds up their contributions.

> **노트.** 계산하는 것은 θ의 오차 프로파일을 π의 오차로 옮기는 부분합 공식이다. 구간 [300, 330]을 셀로 나누고 셀 기여를 더한다.

## 3. A real numerical source

`Solutions/Table4Evolution.v1/c/qrh_trunc2.c`, after the frozen summation loop (identical, byte for
byte, to the loop proved correct in round 1):

```c
static const double inputs[2] = {
    0.7999073965026894939001067541539669036865234375,
    0.036628287383099832064115020102690323255956172943115234375
};
double fks2_table4_transport(void) {
    double s = sum(inputs, 2);
    double r = (s * 0.0000000000000000277555756156289135105907917022705078125);
    r = (r + 0.000000000000000000000000176650896692503576590208711096…);
    r = (r + 0.000000000000000468375392525011201421143379094323659735…);
    r = (r + 0.000000000000000001427973757698204816618073176699030809…);
    return r;
}
```

| Literal | Meaning | How it is justified in Lean |
|---|---|---|
| `0.79990…` | `2^55·` (upper bound of the cell `[300, 329]` with `U = Q(300)`) | exact rational Taylor enclosures of `e^{-9.6…}` and `e^{-16.9…}` (`cellsOK`) |
| `0.03662…` | `2^55·` (cell `[329, 330]`, `U = Q(329)`) | same |
| `0.0000…277` | `2^{-55}`, the scale | exact |
| three constants | anchor, `Q(330)`, `Q(330)/328` | `constOK` |

> **노트.** 실제 C 파일이다. 숫자 하나하나가 무엇의 상계인지, Lean이 어떻게 확인하는지 표로 정리했다.

## 4. Why the C file means what it says

1. **Source identity.** Lean reads the file with `include_str` and checks its tokens against the
   program it reasons about. One changed digit makes the check false (tested).
2. **Model.** Each `+` and `*` is an IEEE binary64 round-to-nearest operation on the decoded
   literals (`PVCore.Exec`). The C compiler and hardware are not modelled.
3. **Roundoff.** The frozen loop's forward error bound is a theorem (round 1); the certificate checks
   the final output plus that error against the bound.
4. **Literals.** A C decimal literal denotes the nearest double to its decimal value. Decoding the
   decimals used to need native evaluation, because Lean's `String.splitOn` does not reduce in the
   kernel. A new decoder (`PVCore.Decimal`) is proved equal to the old one for every string, so now
   the kernel decodes too.

> **노트.** 소스 일치, 실행 모델, 반올림 오차, 리터럴 해석의 네 단계다. 마지막 단계가 이번에 커널로 옮겨져서 native 계산이 필요 없어졌다.

## 5. Old and new execution

| | old program | evolved program |
|---|---|---|
| cells | 30 unit cells `[300+j, 301+j]` | `[300, 329]` and `[329, 330]` |
| output (QRH input) | `4.715·10⁻¹⁶` | `4.930·10⁻¹⁶` |
| registered target `FKS2Numerics.v7.qrh_pi` | `5·10⁻¹⁶`, met | `5·10⁻¹⁶`, met |
| trusted native computations | 4 | 1, or **0** on the kernel route (147 s) |

**Fair reading.** The input change did the mathematics: with the QRH-free θ table the same 30-cell
program gives `1.69·10⁻¹²`, so QRH bought a factor of about 3,600. The evolved program is slightly *weaker*,
but cheap enough for the kernel to check completely. And the cell cut is not QRH's doing: under the
QRH-free table, 3 cells also meet that table's target.

> **노트.** 수학적 개선은 입력(QRH)에서 왔다. 프로그램 진화는 더 약한 상계를 주지만 커널이 전부 확인할 수 있을 만큼 작다. 셀을 줄이는 것은 QRH가 없어도 된다.

## 6. A downstream theorem: primes in short intervals

From the network's QRH θ bounds, Dusart's explicit interval and a 32-step ladder of primes checked
by the kernel:

> **Theorem** (`QRHGlobal.global_interval`). Under QRH, for every `x ≥ 1` there is a prime in
> `(x, x + x^{7/8}]`. Consequently there is a prime between `n^k` and `(n+1)^k` for every `k ≥ 8`
> and `n ≥ 1`.

With Kadiri–Lumley's table added: a prime in `(x, x + x^{7/8}/16]` for every `x ≥ 1361`, and 1361
cannot be lowered for that constant (no prime in `(1327, 1360.7]`). No native computation is used.

> **노트.** 3차 추정의 예: QRH 아래에서 모든 x ≥ 1에 대해 (x, x + x^{7/8}]에 소수가 있고, 따라서 k ≥ 8이면 연속한 k제곱수 사이에 소수가 있다. native 계산 없이 커널이 확인한다.

## 7. Limitations, stated plainly

- QRH and the analytic inputs of the network's QRH chain are **assumed**, not proved.
- The Table 4 π bounds are **not** the network's best at `e^330` (`≈ 1.6·10⁻²⁰` by partial
  summation; `1.157·10⁻²⁰` from Agent A's program).
- These are local attestations; no official Comparator receipt was produced.
- The C compiler, operating system and hardware are trusted, not verified.
- No independent reviewer read this round.

> **노트.** 한계: QRH와 그 해석적 입력은 가정이다. Table 4의 π 상계는 네트워크 최선이 아니다. 공식 receipt가 아니다. 컴파일러와 하드웨어는 검증하지 않았다. 독립 리뷰어 없음.
