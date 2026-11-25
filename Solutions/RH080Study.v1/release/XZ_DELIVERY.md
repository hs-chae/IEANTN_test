# Downloaded evidence bundle

The single evidence attachment uses `.zip.xz`: an ordinary, complete ZIP wrapped
in standard XZ compression. This reduces repeated evidence and manifest bytes
without removing any additional files. The separately attached English HTML is
the primary reading copy; the English paper, Korean summary and TeX source are
supplements inside the bundle.

Decompress the outer layer with a tool that supports XZ, such as 7-Zip, or on a
Unix system:

```sh
xz --decompress --keep RH080_EVIDENCE_BUNDLE.zip.xz
```

This command retains the downloaded file and refuses to overwrite an existing
ZIP. The final published release receipt records both the XZ and decoded ZIP
SHA-256 hashes. Verify the decoded ZIP before extracting it:

```sh
python3 /absolute/checkout/Solutions/RH080Study.v1/release/verify_bundle.py \
  --archive /absolute/download/RH080_EVIDENCE_BUNDLE.zip \
  --expected-sha256 DECODED_ZIP_SHA256_FROM_FINAL_RELEASE_RECEIPT \
  --extract /absolute/fresh/extracted-network \
  --receipt /absolute/fresh/archive-verified.json
```

Then read `Solutions/RH080Study.v1/REPRODUCE_FINAL.md` inside that extracted
directory. Its first regeneration step restores the 49 exact generated cell
source files omitted from the compact ZIP; all 278 original mathematical input
hashes are checked. The three separately omitted generic runtime inventories
remain optional for mathematical reproduction and have a pinned fetch script.

The XZ codec, filesystem and hash implementation belong to the trusted software
infrastructure. Decompression, archive identity and source regeneration do not
prove a mathematical theorem. The subsequent source-cold Lean builds and audits
are separate checks. Final archive identity, extraction, materialization and
relocated proof replay receipts distinguish these steps explicitly.
