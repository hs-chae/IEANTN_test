# Reading program-verified numerics in IEANTN

For each program-verified node, IEANTN now shows four labels on the generated node page, next to
the usual `Evidence` row:

| Label | Meaning | Example |
|---|---|---|
| **Evidence method** | *What* the proof verified | `lean-verified-program`: a real C source, matched by tokens to a formal program, executed in the RN64 model, with a Lean correctness theorem taking the output to the statement |
| **Local gate** | *How far* the proof was admitted | `native-assisted: passed` (a local research attestation, **not** a receipt) |
| **Official IEANTN classification** | What the official trust graph relies on, unchanged | `lean-noncompliant` |
| **Official Comparator receipt** | Whether Comparator certified it | `absent` |

**None of these is a green "officially verified" mark.** Official verification still means a
designated `lean-comparator` justification backed by a receipt in `receipts/`.

There are three applications. Each is described at three depths: the mathematics, the
computation bridge, and the audit details. The per-endpoint numbers are in
[PROGRAM_VERIFICATION_INVENTORY.md](PROGRAM_VERIFICATION_INVENTORY.md). The design is in
[NATIVE_ASSISTED_DESIGN.md](NATIVE_ASSISTED_DESIGN.md).

---

## A. Forward Ramanujan quantitative gap

**Mathematics first.**
- Ramanujan's inequality is \(\pi(x)^2 < \frac{ex}{\log x}\pi(x/e)\). Its normalized shortfall
  \(\operatorname{loss}(x)\) is bounded by \(C/\log x\) on every real \(x>e^{3915}\):
  - with the old analytic input (PNT+, lower half from \(e^{3914}\), upper half from
    \(e^{3915}\)), \(C=3914.7\);
  - with the QRH-derived input (coefficients 119 and 131 from \(e^{400}\)), \(C=9.101\).
- These are allowances, not true errors.
- The node docstrings and [RAMANUJAN_WALKTHROUGH.md](../qrh/RAMANUJAN_WALKTHROUGH.md) give the
  exact statements.

**The computation bridge.**
- **Definition.** \(\varepsilon(x)=\varepsilon_{\rm Upper}(M,x)-\varepsilon_{\rm Lower}(m,e^A,x)\)
  is the seventh-order term of the repaired Dudek–Platt criterion.
- **Small example.** For \((m,M)=(119,131)\) its seven terms are \(262\), \(394/3915\), and five
  more. Their sum minus \(134+119\) is \(9.10069\ldots\le9.101\).
- **Hypotheses.** \(M\ge0\) and \(\log x\ge Y\). Every term is monotone in \(\log x\).
- **Conclusion.** \(\varepsilon(x)\le\) budget on the whole ray.
- **Next consumer.** `RamanujanGap.v2` turns the budget into the gap and loss bounds.
- **What the C program does.** It sums seven upward-rounded binary64 inputs, multiplies by 4096
  and subtracts 134 and 119. The generic theorem `ForwardRamanujan.source_linked_upper` bounds the
  exact expression by the output plus the \(\gamma_6\) forward error plus \(10^{-10}\).

**Audit details.**
- Source: `Solutions/RamanujanNumerics.v2/c/updated.c`. Its SHA256 is in the attestation.
- Source match: `ForwardRamanujan.Updated.source_check`. Execution witness: `concrete_execution`.
  Correctness: `ForwardRamanujan.source_linked_upper` and
  `SumStability.c_sum_forward_error_real`.
- Native facts: six, each traced to a `native_decide` token in `Updated.lean` (lines 36, 41, 43,
  50, 60 and 65).
- Attestation: `pv-evidence/RamanujanNumerics.v2.epsilon_budget.native-assisted.local.json`.
- **Status:** `native-assisted: passed`; evidence method `lean-verified-program`; official kind
  `lean-noncompliant`; receipt absent. The old baseline `RamanujanNumerics.v1.epsilon_budget`
  gets the same verdict.
- **The consumer** `RamanujanGap.v2.loss_bound` is a standard-axiom implication with zero native
  facts. It is not program-verified itself, because it consumes the budget as a hypothesis.

## B. FKS2 Table 4 θ→π transport

**Mathematics first.**
- \(E_\pi(x)=|\pi(x)-\operatorname{Li}(x)|/(x/\log x)\le c\) for every real \(x\ge e^{330}\), with:
  - \(c=1.69\cdot10^{-12}\) (old reconstruction: FKS2 Table 3 rows plus an anchor at \(e^{300}\));
  - \(c=5\cdot10^{-16}\) (QRH-derived \(\psi\) bound plus the same anchor).
- The comparison is between certified allowances only. The Phase 2 density route is stronger
  under additional inputs.
- See [TABLE4_WALKTHROUGH.md](../qrh/TABLE4_WALKTHROUGH.md).

**The computation bridge.**
- **Definition.** A profile is 31 whole-tail \(\theta\) allowances \(U_j\). From it,
  \(B_{\rm safe}[U]\) = anchor + 30 cells + \(U_{30}\) + \(U_{30}/328\).
- **Example.** In the pedagogical case \(U_j=10^{-12}\), \(B_{\rm safe}\approx1.0061\cdot10^{-12}\).
- **Hypotheses.** A valid profile and the anchor.
- **Conclusion.** By `FKS2Pair.whole_ray_transport`, \(E_\pi(x)\le B_{\rm safe}\) on the whole
  ray. The C program sums the 30 cell enclosures, which are certified by Taylor `expCheck`, scales
  the sum back exactly, and adds three allowances.
- **Next consumer.** `FKS2.v9`.

**Audit details.**
- Sources:
  - `Solutions/FKS2Numerics.v5/c/fks2_table4_transport.c` (QRH);
  - `Solutions/FKS2Numerics.v6/c/fks2_table4_transport_old.c` (old).
- Association: `FKS2Table4.source_checked` and `FKS2Pair.Old.source_checked`.
- Execution: `FKS2Pair.Updated.concrete_execution` and `FKS2Pair.Old.concrete_execution`.
- Correctness: `FKS2Table4.verified_fks2_transport`, `FKS2Pair.source_linked_transport_upper`,
  and `SumStability.c_sum_forward_error_real`.
- 8 native facts per side.
- The provider's explicit hypotheses (QRH ψ bound plus anchor; or the four Table 3 rows plus
  anchor) are listed in each attestation.
- The gate verdicts are in the inventory.

## C. PoC 1: the FKS2 scalar ν correction

**Mathematics first.**
- The FKS2 multiplier \(\nu_{\rm asymp}(e^{30})\) was printed as \(\le 6.3376\cdot10^{-7}\). That
  claim is **refuted**: `FKS2Scalar.original_threshold_discrepancy` proves its negation.
- The corrected statement is \(\le 6.339\cdot10^{-7}\) (`FKS2Numerics.v2.nu_asymp_e30_le`).
- The baseline \(\nu^*(121.096,300)\le1.1\cdot10^{-61}\) and the QRH-updated
  \(\nu^*(10^{-10},300)\le2\cdot10^{-49}\) feed the θ classical bounds of `FKS2.v4` and `FKS2.v5`,
  and from there prime intervals.

**The computation bridge.** The summation stability theory proves a forward error bound for the
selected C sum loop. In the source-linked cases, the executed program
`baselineProgram := if baselineChecked then baselineAST else …` is the abstract syntax tree
**only when** the token check against the real C file succeeds. The proof therefore uses the real
source.

**Audit details.** The decisive finding is that the evidence method differs between the PoC 1
conclusions, although their metadata describes them all alike:
- `FKS2Numerics.v2.nu_asymp_e30_le` and `FKS2Numerics.v3.calibration_bound`: no C source text
  appears in the proof closure. The proof uses the abstract-syntax-tree model of the sum, its
  execution and its error theorem, but nothing ties it to a real source file. They are therefore
  recorded as **`not-program-verified`** (S and A fail), even though the justification id reads
  "source-verified" or "checked-source-stability". Their official kind stays `lean-noncompliant`.
- `FKS2Numerics.v3.baseline_bound` and `FKS2Numerics.v4.updated_bound`: the source literal,
  association, execution and error theorem are all present. See the inventory for each verdict.

---

## English technical summary

- The gate admits exactly:
  - the three standard axioms;
  - per-use `native_decide` axioms (`@Eq Bool e true`) whose declaration range points at the
    `native_decide` token in a hashed project module, and which reach no project
    `implemented_by`/`extern`.
- It rejects `sorryAx`, custom axioms, `unsafe` declarations and unreviewed native mechanisms. It
  also requires the solution statement to equal the generated challenge up to binder names.
- `lean-verified-program` additionally requires the source literal, an association fact, an
  execution witness and a reviewed correctness theorem in the proof closure, plus a mathematical
  endpoint statement.
- Attestations live in `pv-evidence/`. `ieantn.py check` validates them fail-closed.
- Pages show the four labels only when an attestation exists.
- Promotion to `lean-comparator` still requires an authentic Comparator receipt, and therefore
  zero native facts.

## 한국어 요약 (high-level, technical terms in English)

- **세 가지 축.** IEANTN의 numerical program verification을 세 축으로 나누어 표시한다.
  - 공식 trust graph의 **justification kind**는 바꾸지 않았다. 지금 `lean-noncompliant`인 것은 그대로다.
  - **Evidence method** `lean-verified-program`은 *무엇을* 검증했는지를 뜻한다. 실제 C source가 formal program과 token 단위로 일치하고, RN64 model에서의 execution과 Lean correctness theorem이 결과를 수학 statement로 연결하는 경우만 해당한다.
  - **Local gate** `native-assisted`는 *어디까지* 받아들였는지를 뜻한다. 표준 axiom 세 개와, 출처를 감사할 수 있는 finite `native_decide` fact만 허용하는 내부 검사다.
- **Gate의 성격.** Gate는 receipt가 아니다. `receipts/`에 쓰지 않고, `lean-comparator`로 승격하지도 않는다.
- **공식 인증으로 가는 길.** Native fact를 kernel 검증으로 모두 대체한 뒤, Comparator가 진짜 receipt를 발급하는 것뿐이다.
- **Node page 표시.** 각 node page에 네 개 label이 함께 표시된다: Evidence method, Local gate, Official classification, Official Comparator receipt. 그래서 "공식 검증"으로 오해되지 않는다.
- **PoC 1의 발견.** 일부 conclusion은 이름이 "source-verified"이지만, 실제 proof closure에 C source가 없다(`not-program-verified`).
- **Lake의 맹점.** Lake는 `include_str` 입력 변경을 추적하지 않는다. 그래서 C 파일을 바꿔도 build가 성공(stale)할 수 있고, gate의 source hash 검사가 이를 잡는다.
