# Development mistakes

- The first32-module run kernel-checked the actual physical56 witness and
  original-input association successfully, but its copied controller retained
  the old `DEGREE80` receipt label. The unmodified run is preserved as v1;
  the corrected physical56 label receives a fresh final controller replay.
  The mathematical inputs/proof sources were unchanged.
