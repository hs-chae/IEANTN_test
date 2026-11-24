# Clean two-fifths prime-counting corollary

The actual completed spectral Box result implies, for every real `x ≥ exp 100`,

`|IEANTN.primeCounting x - IEANTN.Li x| < sqrt x * (log x / (8*pi) - 2/5)`.

`IEANTN.Li` is the logarithmic integral starting at 2. Both actual prime-power
and integral-offset corrections are paid. The four inputs are exactly RH,
general integrated Perron, Nicolas' spectral bound, and BPT's off-ordinate bound.
They remain explicit published-source predicates; this is not an RH-only proof.

`BoxClassicalScalar.lean` proves the complete function inequality, using an
already proved scalar correction below `14/5` and elementary polynomial bounds.
Reusing that explicit numerical function does not assume the older GM theorem.
`BoxClassicalCorollary.lean` consumes the actual four-source Box theorem and
proves the conclusion both on real logarithms and on the entire real x-ray.
Its canonical wrapper has exactly the four corresponding IEANTN input types.

The subtractive constant improves the earlier clean `1/3` corollary at the same
onset: the exact difference of the two clean right-hand sides is `sqrt x / 15`.
The older and newer source packages differ. No same-premise published-frontier,
optimality, or best-known claim is made. The complete inherited Box function is
stronger than this convenient rounded corollary and is preserved unchanged.

`DERIVATION.html` gives the full functions and all-real algebra with statically
readable mathematics. STIX and its license are embedded for offline use. Both
390px and 1100px browser checks passed; the mobile screenshot was actually viewed
and its Greek/square-root/exponent glyphs are legible. `BROWSER_RECEIPT.json`
records the checks. No browser extension, CDN or external renderer is required.

The two scientific files have twelve written proofs, with eleven selected
printed axiom roots covering the actual claims and supporting numerical leaves.
All have only the standard Lean axioms. The onset examples are kernel proofs:
the complete function is below `3.5704 * exp 50`, the clean `2/5` coefficient
lies between `3.57887` and `3.57888`, and the old clean coefficient lies between
`3.64554` and `3.64555`. These are coefficients of bounds, not computed values of
the actual prime-counting error. No `native_decide`, new axiom or `sorry` is used.
This kernel interval arithmetic is not source-first PV.

## Reproduce

Use the pinned Lean compiler and generic dependencies documented in
`Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json`. The compiler is
Lean `v4.34.0-rc2`, SHA256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`;
Mathlib is commit `71a80585ee495fc24472fd0eaffc89d94e4fd8d6`.

From the network root, with an accepted source-fresh712 run:

```sh
python3 Solutions/RHOcticPush.v1/spectral-076/corollary/reproduce.py \
  --foundation /absolute/accepted/spectral712 --out /absolute/fresh/corollary2
python3 Solutions/RHOcticPush.v1/spectral-076/corollary/reproduce.py \
  --verify /absolute/fresh/corollary2
python3 Solutions/RHOcticPush.v1/spectral-076/corollary/test_reproduce.py \
  --run /absolute/fresh/corollary2 --out /absolute/fresh/corollary-controls
```

The first command recursively validates the entire712 source/object foundation,
freshly compiles both new files without developer or historical application
objects, audits all eleven selected theorem closures, and checks every actual
direct import object. It admits one compiler at a time with a64GiB address cap
and a separately checked512GiB host reserve. Actual per-child peak RSS, owned
storage, commands and source/object hashes are recorded. These are ordinary
kernel proofs, not a verified external C program execution.

To regenerate the source712 foundation from clean pinned generic libraries,
follow the existing composition:
`integration/corrected/reproduce.py` (source454),
`integration/supplement/audit_corrected.py` (source619),
`box/zero/reproduce_zero.py` (source660),
`integration/closed_box/reproduce.py` (source693), and
`integration/spectral_final/reproduce.py` (source712).
Their accepted source captures, exact commands and dependency pins are retained
in the campaign. Each stage has actually passed separately; this study does not
claim a second monolithic clean714 rebuild. No random seed is used.

The accepted append is `/data/ivy-rh-octic-20261123/box-classical-fresh2-v1`,
result SHA256 `f7cf09052046dce4b57bcffe26210da6c93dabaa96dfe5728ddbd6f5fb54393e`.
The two compiler runs took31.933seconds, with8,665,736KiB maximum child RSS,
1,871,695bytes owned before result publication, and zero observed owned-process
OOM events. No aggregate-RSS sampling is claimed. Additional actual CLI controls
are recorded separately when complete. Frozen scientific sources, original
failed attempts, accepted proof artifacts and concise reproducibility evidence
are retained; only checked reproducible copied control fixtures are cleanup
targets. No prime lists or large numerical certificates are generated here.

The actual 33 normal/`-O`/`-OO` controller decisions have completed and their
stdout/stderr hashes, return codes and required rejection messages were read
back. See `evidence/controls33-v1/RESULT.json`. This historical test used an
explicitly checked sibling output and did not test nested output rejection;
the additive feedback test adds that preflight and three corresponding CLIs.
Original accepted proofs, controller source and test history remain unchanged.
