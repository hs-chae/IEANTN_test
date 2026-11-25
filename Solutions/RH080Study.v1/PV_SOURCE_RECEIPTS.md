# Source-first C verification receipt guide

Exactly one new numerical C program is source-first verified here: [dual_grid.c](pv/dual_grid.c), SHA-256 `da11ed48a9596134df48f29066299b39c458ac891daa90b9380dcca469ea7feb`. It computes 257 grid maxima from20 rational jumps and nine-term fixed-point sine calculations, rather than returning an assumed final constant. Its actual output is `1221161\n` at scale10^6.

The complete [handoff](pv/HANDOFF.json), [source-only45-module receipt](pv/receipts/fresh-joint-v2-j2/RESULT.json), [README](pv/README.md) and [minimal49-module canonical cone](pv/V1_PROOF_CONE_MANIFEST.json) identify the actual grammar, syntax theorem, UInt64 source execution, reachable overflow/underflow/division guards, 129 true-sine enclosures, 257-point maximum, continuum chord/tail argument and canonical consumers. The final numerical ratio theorem consumes the actual source-computed cap. Std3 are the only axioms in accepted roots; no native execution axiom remains.

Fresh C compilation/execution at O0/O2/O3 and UBSan agrees byte-for-byte. These executions support applicability and reproducibility; they do not prove compiler correctness. Generic selected-C semantics, compiler/header/ABI/libc/OS and hardware adequacy remain explicit boundaries. Failed or partial printf is modeled: return0 does not imply stdout success, as an actual `/dev/full` negative case demonstrates. Exact serialized stdout is conditional on the performed successful printf contract and separately observed in compiled runs. The numerical cap itself does not depend on stdout success.

The source-to-grammar theorem is not equality of two token lists alone. Its target is an independently specified syntactic relation reused from the Goldbach frontend. It covers precisely the actual restricted scalar C fragment; no claim is made about all C++ or CUDA.

This C proof establishes a restricted L1 Fourier-functional obstruction, not a prime-gap lower bound or unrestricted optimizer theorem. Gaussian degree80/56 integral calculations and cube numeric inequalities are **D kernel-only**, not PV. External Arb replay is E evidence, not PV. V0 has the same numeric values; this study does not establish a numeric or causal superiority of source-first PV.

Use [REPRODUCE.md](REPRODUCE.md) and `reproduce_study.py --lane pv`, followed by the canonical proof consumer lane. The full C AST proof used about96.64GiB process RSS; a64GiB address-space attempt failed with bad_alloc/SIGABRT, not an OOM kill. Actual commands, compiler pins and source/certificate/object hashes remain in the receipts.
