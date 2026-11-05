# Tertiary estimates under QRH, verified

For a reader who knows analytic number theory and not program verification. QRH is the hypothesis
that `ζ(s)` has no zeros with `Re s > 7/8`. Every statement below is a Lean theorem that was compiled
and whose axioms were printed; QRH and the network's literature inputs enter as hypotheses, and no
step trusts native code unless stated.

> **노트 (한국어).** QRH(제타 함수의 영점이 Re s > 7/8 영역에 없다는 가정) 아래에서 얻은 3차 추정 결과를 정리했다. 모든 정리는 Lean으로 컴파일했고 공리를 확인했다. QRH와 문헌 입력은 가정으로 들어간다.

## 1. A Mills constant with explicit digits

Mills (1947) showed that there is `A` with `⌊A^{3^n}⌋` prime for every `n`. His construction needs a
prime between consecutive cubes, which is known unconditionally only for all sufficiently large cubes
(explicit versions start astronomically far out), so the start of the sequence, and with it the
digits of `A`, are not explicit; the usual value `1.30637788…` assumes RH.

Under QRH every interval `(x, x + x^{7/8}]` with `x ≥ 1` contains a prime, which puts a prime between
`q^8` and `(q+1)^8 − 1` for **every** `q ≥ 1`. So the construction runs from `p₀ = 2`:

> **Theorem** (`QRHGlobal.mills_explicit`). Under QRH there is `A` with `⌊A^{8^n}⌋` prime for every `n ≥ 0`,
> `⌊A⌋ = 2`, `⌊A^8⌋ = 257`, `⌊A^{64}⌋ = 19031147999601100901 = 257^8 + 100`, and
>
> `A = 2.00097489763307733758…` (precisely `2.000974897633077337586 ≤ A < 2.000974897633077337588`).

The same holds for every real exponent `k ≥ 8` and from every starting prime (`mills_qrh`). The
20-digit prime is certified inside Lean by a Lucas certificate (`2` generates; `p − 1 = 2²·5²·222799·854184623791`),
with the modular powers computed by Lean's kernel.

> **노트.** 밀스 상수: ⌊A^{8^n}⌋이 모든 n에 대해 소수가 되는 A를 QRH 아래에서 구체적으로 구했다. A = 2.00097489763307733758… 처음 세 항은 2, 257, 19031147999601100901이다. 고전적인 밀스 정리(지수 3)는 시작점이 명시적이지 않지만, QRH에서는 지수 8 이상이면 어떤 소수에서든 시작할 수 있다.

## 2. How many primes are in `(x, x + x^{7/8}]`

The prime number theorem predicts about `x^{7/8}/log x` primes there.

> **Theorem** (`QRHGlobal.count_300`). Under QRH, for every `x ≥ e^{300}`, with `N = π(x + x^{7/8}) − π(x)`:
>
> `0.9737·x^{7/8} ≤ N·log(x + x^{7/8})` and `N·log x ≤ 1.0263·x^{7/8}`.

So every such interval holds the expected number of primes up to 2.6%. With Agent A's bound on `π`
(a separate, program-verified input) the window is `[0.98105, 1.01895]`. Two general theorems produce
these from any power bound on `Eθ` or on `Eπ` (`count_of_theta_power`, `count_of_pi_power`).

> **노트.** 짧은 구간 (x, x + x^{7/8}]에 있는 소수의 개수를 위아래로 잡았다. x ≥ e^300이면 예상 개수의 97.4%에서 102.6% 사이다.

## 3. Short intervals, and how short

| From | Interval | Sharp? |
|---|---|---|
| every `x ≥ 1` | `(x, x + x^{7/8}]` | (round 3) |
| every `x ≥ 1328` | `(x, x + x^{7/8}/16]` | yes: `1327` fails |
| every `x ≥ 1339` | `(x, x + x^{7/8}/24]` | yes: `1338` fails, no prime in `(1338, 1360.67]` |
| every `x ≥ e^{300}` | `(x, x + 0.019·x^{7/8}]` | (from Agent A's `π` bound) |

`1/24` is as far as the network's present tables go: at `x ≈ e^{160}` the QRH coefficient of `θ`
forces the constant above `0.0414`.

Analogues of two classical conjectures follow, with squares replaced by `k`-th powers (`k ≥ 8`) and
square roots by eighth roots: primes in `(n^k − n^{k−1}, n^k)` and `(n^k, n^k + n^{k−1})`
(Oppermann-type), and `p'^{1/8} − p^{1/8} ≤ 1/8` for consecutive primes, `≤ 1/192` once `p ≥ 1339`
(Andrica-type).

> **노트.** 구간 상수를 1/24까지 줄였고, 시작점 1339는 더 낮출 수 없다(1338에서 실패한다는 것도 증명). 오퍼만, 안드리카 추측의 7/8 버전도 얻었다.

## 4. How the numerical program evolved

The Table 4 computation turns a bound on `θ` into a bound on `π` by partial summation. Its program
has had three versions:

| | cells | output | proof |
|---|---|---|---|
| FKS2 (round 1) | 30 | a constant: `Eπ ≤ 4.7·10⁻¹⁶` for all `x ≥ e^{330}` | 4 native facts |
| round 3 | 2 | a constant: `Eπ ≤ 4.9·10⁻¹⁶` | kernel only |
| **now** | **0** | **a decaying bound**: `Eπ ≤ 0.013156·x^{-1/8}` for all `x ≥ e^{330}` | kernel only |

With a power-law input `Eθ ≤ K·t^{-1/8}` the integral has a closed-form majorant (`κ·t^{7/8}/log² t`,
`κ = 600/521`), so the cells disappear: the program adds two numbers and one constant. Its output now
decays, and a decaying `π` bound can feed the Ramanujan budget, which a constant cannot. That made a
three-program chain possible: Agent A's `θ` program → this transport → the budget program, proving
`(1 + 7.84/log x)·x²/log⁶x < (e x/log x)π(x/e) − π(x)²` for `x > e^{331}`.

> **노트.** 프로그램 진화: 셀 30개 → 2개 → 0개. 입력이 거듭제곱 꼴이면 적분을 닫힌 형태로 잡을 수 있어 셀이 필요 없다. 출력이 상수에서 감소하는 상계로 바뀌어 세 프로그램 연쇄(θ → π → 라마누잔)가 가능해졌다.

## 5. Less trust in native code

Twelve program results now need no native evaluation at all: the decimal literals of the C files are
decoded by the kernel, and every certificate is checked by the kernel (45 s to 264 s, up to 37 GB).
Among them are three registered network statements (`FKS2Numerics.v6.old_pi`,
`RamanujanNumerics.v1/v2.epsilon_budget`). In round 3 there were two.

> **노트.** native 계산 없이 커널만으로 확인한 프로그램 결과가 2개에서 12개로 늘었다. 그중 3개는 네트워크에 등록된 명제다.

## 6. Limitations, stated plainly

- QRH and the analytic inputs of the network's QRH chain are **assumed**, not proved.
- Mills' theorem itself is classical; the gain is explicitness under QRH, not existence.
- The Table 4 π bounds are second routes: Agent A's own π bound is better by 3.6% at `e^{330}`.
- The three-program chain re-proves Ramanujan's inequality on a range the network already covers
  (from `e^{145}`); it demonstrates composition.
- These are local attestations; no official Comparator receipt was produced. No independent reviewer
  read this round.

> **노트.** 한계: QRH는 가정이다. 밀스 정리 자체는 고전적이고, 새로운 점은 명시성이다. 세 프로그램 연쇄는 이미 알려진 범위의 라마누잔 부등식을 다시 증명한 것으로, 합성의 시연이다. 공식 receipt는 없고 독립 리뷰어도 없었다.
