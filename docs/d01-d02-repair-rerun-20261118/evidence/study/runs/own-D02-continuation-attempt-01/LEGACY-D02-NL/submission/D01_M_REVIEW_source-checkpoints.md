# Source checkpoints and reproducibility map

The review binds FOLLOWUP-C021 / FOLLOWUP-D01. Verification of SHA-256 for all
66 exact packet payloads and the original source PDF and extraction pairs was
completed. Full hashes and alias mapping are in review.json; the table below
gives reproducible locations in the supplied source text extractions (physical
LF numbers, with original page numbers when material). The original PDFs
remain authoritative. No independent PDF renderer is installed in this
runtime; the page-marked formula extractions were sufficient for the formulas
invoked. In particular the possibly misleading small-x CH2 (9.1) display and
low-delta raw FKS parameters are not used to generate any required constants.

| Original | Checkpoints in its extraction and original pagination |
|---|---|
| OpenAIQRH | LF 234 (modulo-1 character); 255–262 (Thm 1.1, p.4, open right half-plane and its actual scope). Retained at admitted trust; not a new verification of the paper. |
| PlattTrudgianFiniteRH | LF 47–51 (Thm 1, p.2); 128–150 (Cor.1 domains, p.4); 181–185 (reported π<li and θ<x, §3.3 p.5). |
| PlattTrudgian2021 | LF 77–117 (Thm 1/Cor.1, A+0.1 for θ); 135–212 (Table 1 and exact Ramanujan wording, p.3); 234–246 (Lemma 2, exact normalization p.4); 724–807 (§5 and small-range Lemma 6 p.9); 984–985 (large ray p.11). |
| DudekPlatt2015 | LF 52–55 (Thms 1.2 and 1.3, p.2); 561–588 (sign and normalization context p.8); 589–649 (§3.1 and stepping); 698–715 (original computation and Lemma 3.4 p.10). |
| CH2 | LF 190–240 (Cor.1.2–1.3, p.3, both ψ and harmonic Λ, exact center and slope); 5040–5052 and 5125 (finite part at 1 and special value at 0); 5216–5223 (ψ extrema, Lemma 9.2 p.35); 5273–5307 (center correction and proof of Cor.1.3, p.36); 6340–6356 (B.5/B.6 p.44); 6801–6819 (B.9 p.46). |
| FKS | LF 113–143 (Thms 1.1–1.2, Cor.1.4); 266–345 (zero counts and reciprocal bounds pp.4–5); 520–527 and 586–607 (raw hypothesis vs published table conclusion); 631–648 (Thm 3.2 and Remark 3.3, pp.8–9); 683–702,729–745,811–847,879–903,1093–1138,1150–1175 (zero-sum partitions and bounds in §3); 1752–1772 (§4, T choice and table columns); 2303–2315,2387–2407 (Table 5 p.22); 2578–2588,2603–2612 (Table 6 p.23); 3136–3258 (Table 8, p.26, with applicable coefficients distinguished from raw parameters). |
| Dusart2018 | LF 171–189 ((2.1), pp.3–4 and jump convention); 246–257 (Thm 2.3 p.5); 958–1016 (Thm 4.2 and 1.4262 prime-power input p.11); 1048–1056 (Prop.4.3 p.12); 1094–1137 (Prop.4.4, Cor.4.5 p.13); 1283–1287 (original π<li report); 1413–1427 (Prop.5.4, Cor.5.5 p.16); 1479–1553 (Thm 5.6 and positive transfer kernel pp.17–18); 1555–1586 (Thm 5.7 and B3, p.18); 1633–1751 (Remark 5.8, Thm 5.9, p.19–20). |

## Evidence and restart facts

- Initial `pwd; ls -l /task/{INPUT_CONTRACT,RUNTIME_PATHS,CANDIDATE_INDEX}.json`
  printed the assigned directory; ls was absent (127). Non-login Bash tests
  confirmed readability and Python read the packet. No network and no other
  candidate.
- Restored exact original basenames under `/work/exact` by the authorized
  script. Reconstructed a source-identity LOCK for the replay from
  CANDIDATE_INDEX (the original standalone LOCK was not mounted).
- Executed the original launcher, default mode, once to completion. Tabs of
  raw stdout, hashes and exact subcommands in receipts.json; stderr of the
  parent replay was empty. All named counterpart outputs match candidate
  receipts in 027 (tag spelling differs for the D02 child scripts).
- Directed tests are distinct from analytic arguments that identify their
  covered intervals. The C scan reaches 100000000; the D02 independent
  Python scan reaches 268435456 and checks the final constants. No published
  zero table or giant PT literature interval was regenerated.
- Auditor's supplemental source/endpoint arithmetic ran to completion
  separately. No new core analytic work or parameter search. The protected
  current candidate exact bytes did not change.
- review.json is the completed mathematical inventory; the closed log
  endpoints, strict inequalities and auxiliary weaker-premise gap are
  explicitly distinguished from unfinished assessment. No handoff pending.

## Mechanical readiness follow-up

The readiness check reported “claim family identity required” without a
mathematical judgment. The nine already-assessed tertiary rows now use
one of the two required family identifiers: prime-count and short-interval
rows are attached to Ramanujan, and product/primorial/totient rows to
Mertens. All nine are explicitly secondary and unscored, outside both
strongest-supported portfolios. No conclusion, proof, receipt, candidate
byte, or per-claim mathematical status was changed by this relabeling.
