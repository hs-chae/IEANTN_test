# Preserved unsuccessful steps

* Initial Lean development used a partial supplement object directory before the
  complete inherited union. Lean correctly rejected missing IEANTN.Vocabulary.Zeta;
  the failed source-command output is retained in the owned scratch evidence.
* Taylor/scalar proof development produced several ordinary elaboration failures
  (extra ring after field_simp had closed a goal, and mechanical copied constants).
  No failed compile was counted as accepted. Corresponding stdout/stderr remain.
* Initial canonical higher-power adapter omitted Nat.cast_add and the explicit
  primesBetween alias unfold. Kernel elaboration rejected it; failed source and
  logs are preserved. The corrected complete Solution and actual body audit passed.
* The optional pdftotext executable was unavailable. No source acceptance used its
  failed output; installed PyMuPDF independently extracted the actual primary PDFs.
