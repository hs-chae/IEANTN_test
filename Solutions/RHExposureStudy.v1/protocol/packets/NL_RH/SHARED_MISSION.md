# Shared mathematical mission: explicit consequences of RH

Assume the precise RH statement below. Develop the strongest defensible explicit analytic-number-theory consequences you can obtain for the shared target questions, including useful downstream applications. You may read legitimate mathematical literature, introduce justified additional source inputs, compute, write programs, use Lean, and develop new methods with the tools available in your environment.

Prioritize mathematical strength: bounds, onsets, validity ranges, quantitative margins, independent assumptions, and useful consequences. Compare against known RH literature. Label imported results, rediscoveries, new deductions, and verification improvements separately.

Record exact statements, domains, hypotheses, sources, actual computations, proof status, and failed approaches. Document real reuse and any recovery of information that a specified earlier argument did not exploit. Do not call certificate checking or native computation source-first PV unless an actual program is connected to formal execution semantics.

Continue beyond familiar textbook consequences. Work independently within your assigned inputs and tools. Do not attempt to access another arm or hidden evaluator materials. Save reproducible candidate statements and evidence at the scheduled checkpoints.

## Common RH and definitions

Use the pinned Mathlib RiemannHypothesis, in Mathlib.NumberTheory.LSeries.RiemannZeta. It asserts: for every complex s, if riemannZeta(s)=0, s is not any negative even integer -2(n+1), and s != 1, then Re(s)=1/2. This is an explicit hypothesis, not a theorem proved by the experiment. Account for boundary/pole/trivial-zero conventions in any adapters. Do not strengthen RH to GRH or assume numerical zero sums, prime tables or unproved coefficients.

For real x use the ordinary right-continuous functions pi(x)=#{p prime:p<=x}, theta(x)=sum_{p<=x} log p, psi(x)=sum_{p^k<=x} log p. Define Li2(x)=integral_2^x dt/log t (x>1); if a source instead uses li(x), include the additive normalization constant explicitly.

Use Epsi(x)=|psi(x)-x|/x and Epi(x)=|pi(x)-Li2(x)|/(x/log x), where meaningful. For Ramanujan use G(x)=(e*x/log x)*pi(x/e)-pi(x)^2 and RG(x)=(log x)^6*G(x)/x^2.

## Shared target questions (all four)

PNT: Find useful complete explicit bounds for psi, theta and pi, with precise hypotheses, onsets, validity ranges and pointwise comparisons. Investigate multiple serious methods, including RH-specific estimates and legitimate refinements of existing inputs. A formal parameter specialization outside its domain is not an accepted improvement.

Intervals: Derive useful prime-existence, prime-count-in-interval, or inverse prime-count consequences, comparing with strong applicable direct RH literature rather than only a weak PNT corollary. Check both endpoints and all inversion/domain restrictions.

Weighted: Pursue explicit weighted Chebyshev sums, Mertens sums/products, or another genuinely connected downstream family. Seek complete useful functions and ranges; retain signed or shared information where it helps and justify every new input.

Ramanujan: Seek a strong explicit positive lower envelope for G or RG, an earlier analytic onset, meaningful complete all-real coverage, fewer independent hypotheses, or a better verified finite algorithm. Distinguish real/integer coverage and strict endpoints. Compare with actual Dudek-Platt and Johnston literature, including prior computation; do not call a known theorem new mathematics or a cited computation source-first PV.

Open discovery beyond these four is welcome when connected and mathematically substantive. RH alone is neither GRH nor binary Goldbach. Do not assume desired conclusions as source predicates. No optimality/best-known claim is required.

## Common source access

Both arms start with identical original PDFs and page-marked text for Lee-Nosal arXiv2312.05628v4, Dudek-Platt arXiv1407.1901v1, Johnston arXiv2109.02249v2, under /corpus/literature. This is a starting catalog, not a closed bibliography. You may request ANY relevant legitimate original mathematical source or genuine supplement, and search for later improvements, using /task/request_source.py. For example:
  /usr/bin/python3.10 /task/request_source.py --id new-source --url https://arxiv.org/pdf/IDENTIFIER
  /usr/bin/python3.10 /task/request_source.py --id search-topic --query 'specific mathematical literature question'
Requests are delivered only to your arm; the neutral broker adds original source bytes/metadata to /corpus/literature/admissions/ID. The other arm's requests, findings and explanations are not shared. Never infer a mathematical fact from a failed fetch. Raw HTTP, browser, host files and connectors are unavailable. Request latency and source admissions are recorded.

## Common work and checkpoint rules

You have the same generic Lean4.34.0-rc2/Mathlib71a80585 and compiler/Python/symbolic numerical facilities, 8 CPUs, 96GiB per-run memory, 64GiB scratch initially. These are substantial initial allocations, not mathematical limits; document a justified larger task for the coordinator rather than weaken claims. No artificial output/token/operation cap terminates research. Passive technical snapshots every60 seconds and comparison checkpoints at900,1800,3600 seconds. The first submission must include serious multi-route improvement attempts in all four families and at least3600 seconds of research opportunity; later own-arm continuation is permitted symmetrically. Do not spend time waiting merely to reach a clock threshold; pursue the mathematical work.

Save flat source/proof/derivation/result files under /work/submission, together with STAGE_STATUS.json {"ready_for_review":true,"serious_attempts_documented":true,"families":{"PNT":{"status":"supported|incomplete|no_additional_improvement"},"Intervals":{"status":"..."},"Weighted":{"status":"..."},"Ramanujan":{"status":"..."}}}. Every result records exact definitions, constants, quantifiers/domains, all hypotheses, primary locators and actual proof/execution status. Include failures and limitations; numerical plots or sampled calculations are exploration, not all-real proofs. LOCK.json contains {"files":[{"path":"filename","sha256":"..."},...]}, including STAGE_STATUS.json. A submission is unreviewed until independently checked.
