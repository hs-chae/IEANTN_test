# Exact publication provenance

The complete offline evidence archive is 352,175,549 bytes, SHA-256 `a332f37373cfe5afb0c5800b5b62fa426671d42c3ed1370dcd26d0d99dca9b3d`. Its 53 numbered parts and all 7,968 archived member identities are recorded in [PUBLIC_MANIFEST.json](PUBLIC_MANIFEST.json). The complete archive and parts are delivered separately to the study owner and are not committed in this reading copy.

[PUBLIC_EVIDENCE_INVENTORY.json.gz](PUBLIC_EVIDENCE_INVENTORY.json.gz) preserves the exact source inventory used for that build. Its decompressed SHA-256 is `43a18a70eacef78465e8a50c31699c5f84f9dbc267e094d84b0a431fbdf27e94`. [ROOT_PACKAGE_BUILD_AUTHORITY.json](ROOT_PACKAGE_BUILD_AUTHORITY.json) preserves the exact approval, SHA-256 `ee8ab8e3c0a022b9cae5492cfc575618c3e1a72a8535d8d5a628b5777cf4007e`. These are outer provenance sidecars, avoiding recursive inclusion in their own archive. Historical absolute source identities resolve to selected restored bytes through `PUBLIC_SOURCE_MAP.json`.

The [actual metadata validation receipt](evidence/publication-metadata-validation/RESULT.json) records 42 CLI checks: three accepted current-inventory runs and 39 rejection controls under normal Python, `-O` and `-OO`. This is publication metadata validation, not a new mathematical experiment or proof. Its code and exact output/error streams are preserved alongside the receipt.

The complete bundle contains all eleven pinned plotting wheels and the frozen paper library. The repository copy conservatively omits the fourteen original-paper PDF/text files and all eight selected archives/wheels containing PDF members, including both copies of the plotting wheel with nested PDF assets. See the reading-copy selection receipt for exact exclusions. Mathematical text, MathML and SVG content are preserved; only reading-copy source links and placement notices change.

The [scientific checkpoint](CHECKPOINT.json) and [current study entry](index.html) separate scientific completion from subsequent cleanup, remote-publication and downloaded-attachment receipts. Original experimental outcomes and negative history remain unchanged.
