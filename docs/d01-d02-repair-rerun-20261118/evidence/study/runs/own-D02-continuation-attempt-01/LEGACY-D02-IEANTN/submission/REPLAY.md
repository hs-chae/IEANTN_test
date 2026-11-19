# Reproduction, statuses, and restart note

## Offline setup and interruption log

First command was `pwd; ls -l /task/INPUT_CONTRACT.json /task/RUNTIME_PATHS.json` under non-login /bin/bash. It confirmed the supplied cwd; the ls part exited 127, exactly "/bin/bash: line 1: ls: command not found". Recovered immediately with bash printf and /usr/bin/python3.10 directory enumeration and file reads. The locale emitted a C.UTF-8 warning; set LC_ALL=C for future reproductions. The ordinary `pdftotext` executable also was not on PATH; used the pinned, hash-checked PDF/text pairs shipped in the corpus. All seven PDF and all seven extraction hashes were validated using SOURCE_INDEX.json. Only the assigned mounted material and offline executor were used. No delegation or external information was requested. There is no unrecovered packet-access interruption. Usage counters beyond executor records are not inferred from the planning numbers.

## Exact own-history restoration

Authorized previous material C003 (D01) and C011 (D02) was restored to /work/own/D01 and /work/own/D02 with:
`/usr/bin/python3.10 /task/RESTORE_OWN_HISTORY.py --out /work/own`
(on a fresh path). This verifies supplied exact byte identities. This research first used D01's power-bound and low-onset floor, then examined the C011 late and finite links using that validated floor. The full source, both prior reviews and source feedback were rechecked; the historical provenance is not a blind baseline. The prefixed historical copies in this submission are ancillary; C++ include names were adjusted for the flat directory. For original-byte replay use the restored paths, avoiding module-name collisions. The old review files contain the precise receipt plans and commands.

Fresh replays completed of D01 cert.py, ram.py, tails.py, smooth.py, endpoint.c/endpoint.py and the six sieve.c runs, including [1000,72004899338]. D02 analytic.py ./count and mcheck.py replayed (conditional portions are *not* claimed for this input), all eight bridge.cpp intervals, and finite Mertens m0 through m8 with the original parameters. Run the exact argv in the corresponding /task/D01__PRIOR_EVIDENCE_REPLAY_PLAN.json and /task/D02__PRIOR_EVIDENCE_REPLAY_PLAN.json, adjusting workdirs to the restored paths and building with the named /usr/bin/gcc or /usr/bin/g++ (use C++17 for D02). Do not use the historical paths to any mount not listed in RUNTIME_PATHS.json. replay_history.log records the current actual stdout hashes/results. It does not imply that the original literature's separate finite computations were run.

## New exact checks

From /work/submission, without optimization of Python assertions:
```
/usr/bin/python3.10 -B ram_repair.py
/usr/bin/python3.10 -B m_repair.py
/usr/bin/g++ -O3 -std=c++17 -pthread m_coarse.cpp -o /work/m_coarse
/usr/bin/g++ -O3 -std=c++17 -pthread d02_mexact.cpp -o /work/mexact
/usr/bin/g++ -O3 -std=c++17 -pthread m_onset.cpp -o /work/m_onset

/work/mexact 2278381730 2278382 20000
/work/mexact 2278381940 3500000 19998
/work/m_onset w 912559998 2278383 3000000
/work/m_onset w 912560000 2278383 2999999

# usage: m_coarse <top> <integer coefficient × 100000> <start> <mesh divisor>
/work/m_coarse 9000000000   1100  3000000000 5000000
/work/m_coarse 11500000000  1000  4760000000 10000000
/work/m_coarse 13000000000   900  8500000000 7000000
/work/m_coarse 18000000000   800 12000000000 6000000
/work/m_coarse 26500000000   700 16000000000 5000000
/work/m_coarse 35500000000   600 22000000000 5500000
/work/m_coarse 61000000000   500 30000000000 5000000
```
Compare to replay_new.log; do not use coarse exit code as evidence for the full input interval. In the first run the largest failed right endpoint is 3909288921 and the verified suffix starts there; fifty or more bins passing or even millions of passing bins would not by themselves certify another onset. For all later claimed runs there are zero failed cells. The Python checker prints floats only as diagnostics after deriving exact rational bounds. No finite join or whole-ray step uses a grid of approximate pointwise samples.

Diagnostics in that log include t11 or t10/t09 (refined) versus m10/m09 (looser); m09 was started earlier and its unresolved cells do not certify a .009 ray there. The m11 historical checker with looser constant but finer mesh (top 10^10, coefficient numerator 11/1000, start 4200000000, divisor 8000000) has zero failures and thus separately covers the originally disputed 4760000000 onset at .011. tr1–tr4 tried extending D1 near the product onsets by adjusting the start guard to 2260000; these sufficient checks did not justify the same earlier D1 claim. tw is an attempted .29999 at 912560; tw4 tries .3 at 912559.995; neither was promoted to a theorem. The corrected stronger supported step takes the still smaller coefficient where its proof succeeds and the earlier x=912559.998 where certified.

## Remaining technical bottlenecks

* Premise gain cannot be manufactured by optimization: B0 implies the hypothesis with the exact correctly quantified threshold, domain and constant. The historical 27/32 improvements are out of scope as consequences of this input. Both independent-of-input families are improved; no related branches are counted as independent evidence for the added input.
* Ramanujan: the late plateau/power switch near L=189 is the loss bottleneck for raising the uniform 1+14/L+8/L² profile at the displayed onset, despite much stronger local margins on the 48–59 interval. An attempt with +10 for the entire join failed; split any stronger local claims. The high-order approximation formally stops where the retained positive coefficients and analytic error budget no longer pay for the proposed margin. Local endpoint optimality is exact; global optimality of margins/onsets is not claimed. The long published finite π computation and underlying PNT zero information have not been independently replayed.
* Mertens: pushing finite onsets earlier or coefficients lower requires interval slack near individual oscillations/prime jumps, not just higher mesh density everywhere. Large finite tests with insufficient precision or range were tried and recorded. The signed integral is small in the power tail; the local θ endpoint controls the exponent and log factor. The complete pointwise envelope may always take all available valid branches. Current smaller power/log coefficients are affirmative improvements over inherited constructions, not global lower limits.
* No source-first PV, native_decide, or Lean formalization is claimed. Mathematical certificates use ordinary integer/rational execution together with the written proofs and admitted literature. Independent mathematical review follows. The research stage is ready; no user or supervisor input is needed for replay. If continuing, focus on the CH2-to-power transition at L≈189, independent verification of the inherited DP computation, or adaptive selective plateau checking near unresolved Mertens sufficient-test cells.
