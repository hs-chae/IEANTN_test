# Full missing finite interval: reproducible native scout, not verified prime counts

This directory preserves the actual unchanged adaptive prime-count generator used to test **the entire missing interval [38359837684,640000000000)**. Two complete runs produced 1,240,023 adjacent rows and byte-identical 69,441,288-byte files. This is numerical exploration: the source-model realization of the streaming checker and the truth of its 2,480,042 distinct prime-count queries remain unproved. Neither the generated rows nor ordinary structural checking are called source-first PV or admitted into the verified network.

## Clean native bootstrap

Install Git, CMake, a C++17 compiler, OpenMP and GNU time. The recorded compiler was GCC11.4.0. Use experiment-owned vendor, build and output directories:

```sh
git clone --no-checkout https://github.com/kimwalisch/primecount.git /scratch/primecount
git -C /scratch/primecount checkout --detach 9eb78bc0d1c98129f464db287699532376f52950
cmake -S /scratch/primecount -B /scratch/primecount-build \
  -DCMAKE_BUILD_TYPE=Release -DBUILD_PRIMESIEVE=ON \
  -DBUILD_SHARED_LIBS=OFF -DBUILD_STATIC_LIBS=ON -DBUILD_TESTS=OFF
cmake --build /scratch/primecount-build -j8
python3 reproduce.py --vendor /scratch/primecount \
  --build /scratch/primecount-build --out /scratch/full-finite-native --twice
```

The exact recorded compilation command and library SHA256 values are in `evidence/finite-full-scout-v1/RESULT.json` and `GENERATOR_RECEIPT.json` one directory above. Dependency versions are primecount9.1 and vendored primesieve12.18. The historical `primesieve_commit` field is the enclosing primecount repository commit: it is **not** an independently checked-out primesieve revision. The vendored source tree is pinned transitively by the exact primecount commit. No random seed is used.

## Results and safe cleanup

The two original native runs took137.8941s and151.8954s. Each generated certificate has SHA256 `952647f5576c301ff93078c240ad32dfcdd9b53e1bc52cc1e007ea6f326d412e`. They enumerate22,835,922,604 prime events and8,732,544,478 shifted-prime events. The streaming structural checker checks full endpoint coverage, row adjacency and the strict integer predicate. It counts2,480,042 distinct endpoint queries out of2,480,046 raw queries; deduplication saves only four and does not solve the missing prime-count proof.

With `--twice`, the script checks both full certificate hashes and the complete streaming structure before deleting only its two explicitly named generated files in the newly created experiment output directory. It retains source identity, exact parameters and commands, resource receipts, results and cleanup hashes. It never deletes vendor/build directories, proof artifacts, original research sources or other experiments. Without `--twice`, the generated certificate is retained.

Native peak RSS was7,656/7,752KiB, measured by GNU time. The separate controller monitor reports only the largest1Hz observed cgroup memory sample336,261,120bytes, not a kernel memory.peak value (unavailable on this host). The corrected resource receipt is authoritative about this distinction; the original receipt is preserved as historical provenance. Sampled OOM and OOM-kill counters were zero.
