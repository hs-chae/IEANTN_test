# Compact evidence release

Read the single `RH080_COMPLETE_REPORT_EN.html` first. Korean exposition and English paper/TeX supplements are inside the ZIP. They are supplements, not additional primary reports.

The archive retains exact numerical inputs, actual C and Lean sources, deterministic generators, source-origin manifests, proof/compiled-run receipts, independent reviews and reproducibility commands. Exactly49 large generated Gaussian cell source modules are omitted from the ZIP. Their originals remain in the pinned Git repository and accepted local banks. Separately, three large generic-dependency tree inventories for optional model-runtime reconstruction are fetched by exact immutable URL and SHA-256 using `fetch_optional_runtime_references.py`; they are not mathematical inputs or numeric certificates. All three actual public downloads and all-mode rejection controls were executed successfully. `GENERATED_CELL_SOURCES.json` enumerates exactly the49 omitted mathematical cell source files by path, size and SHA-256; `materialize_generated.py` restores their exact bytes and then checks all278 required mathematical inputs. Restoration is not a Lean proof.

Verify the separately delivered whole-ZIP SHA-256 before extraction:

```sh
python3 -OO Solutions/RH080Study.v1/release/verify_bundle.py \
  --archive /absolute/RH080_EVIDENCE.zip \
  --expected-sha256 THE_SEPARATELY_RECORDED_64_CHARACTER_HASH \
  --extract /absolute/fresh/network \
  --receipt /absolute/fresh/archive-receipt.json
```

The extraction destination and receipt must not already exist. For a first extraction without a checkout, use Python's ZIP tool in a fresh directory after independently checking the delivered archive hash, then run the included verifier with a separate fresh extraction destination. A complete Git clone at the pinned source commit is the alternative and already contains the generated sources.

Next follow `Solutions/RH080Study.v1/REPRODUCE.md`: restore the49 sources, provision the pinned Lean/Mathlib generic infrastructure, then run the mathematical source-only replay. The full C source execution proof needs substantially more than4GiB; its successful receipt records approximately96.64GiB maximum process RSS. No historical application object is required. Optional original-paper supplements, historical baseline campaigns, ordinary Lake packaging and paid/model-service research reruns have separately documented external prerequisites. The compact ZIP is not a replacement for the full IEANTN Git history or external generic dependencies.

`create_bundle.py` accepts only an explicit root-reviewed source/hash/size selection. It produces deterministic regular-file ZIP members. `verify_bundle.py` checks the exact archive hash, member population, manifest, every payload, reserved README and omitted-source population before writing an atomic receipt. These guards establish artifact identity, not mathematical correctness. `test_bundle.py` exercises both actual CLIs under normal Python, `-O` and `-OO`, including changed source/README, duplicate/nonfinite JSON, unpinned commit, path escape, extra payload and reserved-name rejection.

The accepted mathematical proof closures, source-first model applicability, independent source audits and original experimental outcomes have separate evidence. Inherited repository-wide bookkeeping errors are not converted into official Comparator acceptance. New source-first PV is only the C dual program; the Gaussian calculations remain kernel-only numerical proofs. Neither an eventual coefficient below0.8 nor a uniform explicit0.8 ray was proved; the independently checked written0.8 result is a finite prefix through exp(174).

For the optional model-runtime route only, restore the three generic inventories first:

```sh
python3 -OO Solutions/RH080Study.v1/release/fetch_optional_runtime_references.py \
  --repository /absolute/fresh/network \
  --receipt /absolute/fresh/optional-runtime-inventories.json
```

The archived `OPTIONAL_RUNTIME_REFERENCES.json` fixes all three paths, sizes and hashes at the published math-source commit. Existing differing files are rejected and never overwritten. This route requires public network access; it does not call a model. It is unnecessary for any default mathematical proof replay. Original private research traces and the exact paper corpus are preserved locally, with public identities and recipes; they are not falsely advertised as included copyrighted papers or byte-reproducible model-service outputs.
