# Source-preparation corrections

- Two uncompiled physical56 draft comments retained “G40” and “81-position”
  from the preserved v2 template. Corrected them to the actual G28 functions
  and57 positions before any compilation or acceptance. References to G40
  generic coefficient operations remain intentional shared definitions.

- While removing inapplicable v2 compound-bank controls from the new v3 test
  script, the draft lost its closing list/loop delimiter. Python syntax check
  rejected it before any test acceptance. Restored the delimiter; the separate
  frozen cold-replay controller and all mathematical sources were unaffected.
