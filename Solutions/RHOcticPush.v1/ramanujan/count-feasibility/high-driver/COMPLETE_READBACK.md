# Additive complete source and resource readback

The frozen `reproduce_application.py` and its accepted fresh32 output remain unchanged. Its original readback checked copied sources against recorded build hashes, but omitted a second comparison to each frozen scientific source-plan hash and omitted copied C-resource hashes. The actual original files matched; `INDEPENDENT_READBACK.json` recorded that initial independent check.

`readback_complete.py` preserves the original reader and adds explicit checks for all 31 frozen scientific sources, all four copied C resources, the exact generated theorem auditor, the approved pinned generic context, direct application imports in every actual Lean dependency probe, regular-file ownership, and measured child RAM. It checks all 1,079 existing theorem audit rows. This is evidence readback, not another proof or numerical count, and does not establish compiler or runtime adequacy.

```sh
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/readback_complete.py \
  --verify /absolute/completed-fresh32-run \
  --receipt /absolute/fresh-receipt.json
python3 Solutions/RHOcticPush.v1/ramanujan/count-feasibility/high-driver/test_readback_complete.py \
  --basis /absolute/completed-fresh32-run \
  --out /absolute/fresh-control-directory
```

The actual controls passed in normal Python, `-O`, and `-OO`: three positive decisions and 57 rejected mutations. Mutations include rehashed changed Lean source, changed or missing C, an altered generated auditor, empty or incomplete dependency logs, a foreign dependency, false or floating compiler statuses, false durations, changed generic context, historical-cache and numerical-proof claims, duplicate JSON keys in both result objects and theorem payloads, overflowing numeric exponents, and a symlinked C resource. Rejected runs produced no acceptance receipts. Every rejection is checked against its expected gate message. Relocated positive fixtures are synthetic validator inputs; no recompilation is claimed. Controls use fresh regular copies and remove those regenerable copies after checking each decision, preserving commands, stdout/stderr hashes, positive receipts, and the final controls manifest. The accepted original run is never mutated.

The mathematical conclusion of the application replay remains symbolic: the modeled high-input main can execute and successful runs output the mathematical prime count. The separately running exhaustive numerical proof must complete before that value is replaced by 55,206,486,339. The subsequent selected consumer must use the new independent surface-grammar proof and the completed count in its actual Lean proof value. Whole C type/binding/header/compiler/runtime/ABI/OS/hardware adequacy remains a separate disclosed trust boundary.

The independently reviewed first additive reader missed duplicate keys inside theorem payloads and numeric overflow through a valid JSON exponent. Exact v1 code, controls, freeze and receipts remain under `readback-history/v1/` and their original data directories. The v2 reader rejects duplicate keys and all nonfinite JSON numbers, and its new actual controls pass in all three optimization modes. No original scientific source, accepted proof object, original compiler run or numerical result changed.

The v3 fixture driver also rejects control output nested inside the accepted run before creating a directory or copying files. Three actual self-CLI controls check this boundary in normal, `-O`, and `-OO` modes and confirm the forbidden path is absent. Total: 60 CLI decisions, including three positive synthetic relocated fixtures. The strict readback reader itself is unchanged from v2.
