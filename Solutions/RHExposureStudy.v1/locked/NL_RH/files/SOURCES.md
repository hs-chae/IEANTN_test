# Primary sources and data provenance

Read-only files under /corpus/literature. Citations in family files give equation
or theorem locators and identify the specific inequalities retained. This index
lists actual PDF hashes from those mounts, not just candidate URLs.

## Initial packet

- lee_nosal_2312_05628v4: https://arxiv.org/pdf/2312.05628v4; PDF SHA256 `a4aed892f4aa7c59d6e8cf2e3ff6e3b7c950928c59af0b3f234cb2a34e67dc93`.
- dudek_platt_1407_1901v1: https://arxiv.org/pdf/1407.1901v1; PDF SHA256 `dfb317cdcd5bc5475caf35d82d265b1a1a0a228ce712003377e8af1d5003da04`.
- johnston_2109_02249v2: https://arxiv.org/pdf/2109.02249v2; PDF SHA256 `5bc9cafab41c04b0dfc00b9a3963c839f75aea198a58620dc52ffb9e50f6367b`.

## Admitted originals used or consulted

- `admissions/schoenfeld76/SOURCE.pdf`: Schoenfeld, 1976, Corollary 1 (6.18), imported comparator. Requested https://www.ams.org/journals/mcom/1976-30-134/S0025-5718-1976-0457374-X/S0025-5718-1976-0457374-X.pdf; SHA256 `8c3cac1ee52eb05af05ec410adc587a18505a46aacdde41ae097038b0e7c3897`.
- `admissions/rosser75-good/SOURCE.pdf`: Rosser–Schoenfeld, 1975, Lemma 8, smoothed explicit formula background. Requested https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0457373-7/S0025-5718-1975-0457373-7.pdf; SHA256 `d0cc914a4d19b2c113655bf0c0d0ff0e2eba45f9728825ec7be561d7a090817b`.
- `admissions/buthe-small/SOURCE.pdf`: Büthe, arXiv:1511.02032, Theorem 2 (1.5)–(1.10), independent finite computation. Requested https://arxiv.org/pdf/1511.02032; SHA256 `350f96313810ded3e8eaf2af6006b227c8834235e177f49eabb3d43d4931c4d1`.
- `admissions/dgm-candidate/SOURCE.pdf`: Dudek–Grenié–Molteni, arXiv:1503.05403v2, Theorem 1.1 and §1/Perron integral (PDF pp. 1–3). Requested https://arxiv.org/pdf/1503.05403; SHA256 `e311b02a73f64948326d9536b8d94e3d31429d706ddee0a658b38500cea8c190`.
- `admissions/cms-candidate/SOURCE.pdf`: Carneiro–Milinovich–Soundararajan, arXiv:1708.04122v2, Theorem 3, Corollary 4, Theorem 5 and §6 (Brun–Titchmarsh). Requested https://arxiv.org/pdf/1708.04122; SHA256 `45b6c7f991831a2dc456c10285206cb17a53ef46c6ae15e43cfa5671554b0dce`.
- `admissions/ptzeros/SOURCE.pdf`: Platt–Trudgian, arXiv:2004.09765, Theorem 1 (verified height), not rerun. Requested https://arxiv.org/pdf/2004.09765; SHA256 `3362f66af9fa9373977eee70e2282ec33989d5d8b97e0852df9e32cc25b52885`.
- `admissions/bias-candidate/SOURCE.pdf`: Platt–Trudgian, arXiv:1407.1914v1, Corollaries 1 and 2 (one-sided finite sign and global theta/prime-power bounds). Requested https://arxiv.org/pdf/1407.1914; SHA256 `cb4ee24a1f9416252e46e0ffdd8feab2d96ea2e10420d54371ec8ba8514097e0`.
- `admissions/pt-pnt/SOURCE.pdf`: Platt–Trudgian, arXiv:1809.03134v2, Theorem 2 and §5 (Ramanujan, real endpoint issue). Requested https://arxiv.org/pdf/1809.03134; SHA256 `10e7587e4284b9f9130c8a17f888957c5adeed20d054f4d613067e25ea5f0973`.
- `admissions/lamzouri/SOURCE.pdf`: Lamzouri, arXiv:1410.3777, Proposition 2.1 and Lemma 2.3 (Mertens product bias comparator). Requested https://arxiv.org/pdf/1410.3777; SHA256 `1ca0a7792d8f49dd4c8e4c0d6a2fd2f659312765e1c957e1dc9622244e1beba4`.
- `admissions/axler-recent/SOURCE.pdf`: Axler, 2022, DOI 10.7153/mia-2022-25-71, pp. 1149–1151 and Theorem 1.1 (Ramanujan intervals). Requested https://files.ele-math.com/articles/mia-25-71.pdf; SHA256 `4acbe9b901a47b8a532e9ffe4bb11b5504bead02979bb9f90d64fef15c51a75a`.


Johnston's baseline finite-height domain is used only as a literature comparison,
not evaluated outside its parameter range. The initial Lee–Nosal arXiv source
corresponds in title/authors to DOI 10.1016/j.jnt.2025.12.003; no claim of differences
from an unexamined journal text. Axler's 2022 primary source is a different paper
from the earlier Integers citation. Attempts to fetch the latter by guessed URL
returned an unrelated article; no theorem is imported from it.

The source-helper requests initially used a key named value; several broker
attempts demanded a query or url field, so corrected searches/fetches were
recorded with those explicit keys. Some guessed IDs were not the intended papers,
and several publisher requests did not resolve. These and bibliographic results
are not mathematical evidence. See SOURCE_REQUESTS.json and receipts under
/corpus/literature/admissions. Original source bytes were not copied into the
submission. No dependency on another research arm or external computation
channel was used.
