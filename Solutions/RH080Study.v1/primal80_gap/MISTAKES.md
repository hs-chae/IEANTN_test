# Development mistakes and unresolved acceptance

- Cold-v1 resource sampling initially followed only the process leader's
  `/proc/PID/task/PID/children`. ThreadPool compiler children belong to worker
  task child lists, so this undercounted compiler RSS. Live `/proc` inspection
  exposed the mistake before any acceptance. The corrected sampler visits
  every task's children; an independently logged external monitor starts later
  and explicitly reports its partial coverage window. Cold-v1's original
  samples must not be used as aggregate compiler-memory evidence.
- The numerical lane notified a draft G40FullRays generator spelling error:
  `radialGaussian` references had become nonexistent `radialG40` names. Its
  original source snapshot is retained. Only those three references are being
  repaired by the numerical lane; no coefficient, cell, or mathematical
  constant changes. Cold-v1 cannot be accepted against the repaired source;
  final downstream validation must record the new source identity.
- Compound-v2's final console summary accidentally included the long reused-
  leaf association list. The full list remains in its JSON evidence; subsequent
  console output filters it along with the command list.
- The first bad-cell-bank control fixture copied a compound bank whose generic
  objects were intentionally reused, so it lacked their original successful
  compiler logs. The validator correctly rejected that earlier prerequisite
  rather than reaching the intended bad-object guard. The fixture now points
  to the explicitly recorded original cold source/log bank, and each CLI
  stdout/stderr is saved before its expected rejection is checked.
