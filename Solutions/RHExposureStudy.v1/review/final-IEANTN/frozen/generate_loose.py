"""Generate changed theorem slices only from the pinned CH2 proof sources."""
from pathlib import Path
import sys
D=Path('/ieantn/Solutions/CH2.v1')
OUT=Path(sys.argv[1])
OUT.mkdir(parents=True,exist_ok=True)
HDR="""/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Terence Tao and IEANTN contributors; adapted in this study.
-/
"""
for n in ('Section7Vihuela','Section9','Section9Limit'):
    s=(D/(n+'.lean')).read_text()
    if n=='Section7Vihuela':
        a=s.index('set_option maxHeartbeats 2000000 in\ntheorem vihuela')
        z=s[a:s.index('end CH2Section7A',a)]
        z=z.replace('Real.log (T / (2 * Real.pi)) := by','Real.log (T / (2 * Real.pi)) + 0.821 := by',1)
        z=z.replace('≤ 10.3194 := by\n    have := hplatt; unfold PlattZeroSum.v1.inv_ordinate_sum_le at this; exact this','≤ 11.1404 := hplatt')
        content='import Section7Vihuela\nopen Real MeasureTheory Set\nnamespace Loose7\nopen CH2Section7 CH2Section7T CH2Section7A\n'+z+'\nend Loose7\n'
        name='Loose7'
    if n=='Section9':
        a=s.index('set_option maxHeartbeats 1000000 in\n/-- **`prop:sagaro` at')
        b=s.index('noncomputable def ycoth',a)
        # Move only the three affected proofs; all definitions/elementary
        # bounds remain imported from the original proof.
        endA=s.rfind('/--',a,b)
        z=s[a:endA]
        a=s.index('set_option maxHeartbeats 1000000 in\n/-- **`prop:sagaro` with')
        b=s.index('set_option maxHeartbeats 4000000 in',a)
        z+=s[a:b]
        a=b
        b=s.index('/-- **`prop:sagaro`**, in the paper',a)
        z+=s[a:b]
        z=z.replace('CH2Section7A.vihuela','Loose7.vihuela')
        z=z.replace('Real.log (t / (2 * Real.pi))) / Real.sqrt x','Real.log (t / (2 * Real.pi)) + 0.821) / Real.sqrt x')
        z=z.replace('Real.log (t / (2 * Real.pi)) with hV','Real.log (t / (2 * Real.pi)) + 0.821 with hV')
        z=z.replace('Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x','Real.log (T / (2 * Real.pi)) - 0.0005 + 0.821) / Real.sqrt x')
        z=z.replace('  rw [hJsplit]\n  linarith','  rw [hJsplit]\n  simp only [add_div] at hkey1 hkey2 ⊢\n  linarith')
        content='import Section9\nimport Loose7\nopen Complex Filter Topology Set MeasureTheory\nnamespace Loose9\nopen CH2Section6 CH2Section81 CH2Section9\n'+z+'\nend Loose9\n'
        name='Loose9'
    if n=='Section9Limit':
        a=s.index('set_option maxHeartbeats 1000000 in\n/-- **Corollary 1.2, the `ψ` estimate**')
        b=s.index('/-- **The node\'s first conclusion**',a)
        z=s[a:b]
        z=z.replace(' := sagaro_slack',' := Loose9.sagaro_slack')
        z=z.replace('CH2.v1.CT T * Real.sqrt x','(CH2.v1.CT T + 0.821) * Real.sqrt x')
        z=z.replace('Real.log (T / (2 * Real.pi)) - 0.0005) / Real.sqrt x','Real.log (T / (2 * Real.pi)) - 0.0005 + 0.821) / Real.sqrt x')
        content='import Section9Limit\nimport Loose9\nopen Complex Filter Topology Set MeasureTheory\nnamespace LooseLimit\nopen CH2Section6 CH2Section9\n'+z+'\nend LooseLimit\n'
        name='LooseLimit'
    z=content.replace('(hplatt : PlattZeroSum.v1.inv_ordinate_sum_le)',
        '(hplatt : 2 * IEANTN.zetaZeroesSum Set.univ (Set.Ioc 0 20000) (fun ρ : ℂ ↦ 1 / ρ.im) ≤ (11.1404 : ℝ))')
    (OUT/(name+'.lean')).write_text(HDR+z)
