/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.WindowMargin

/-! Quantitative transfer from ANY completed original certificate, including
certificates whose counts come exclusively from the actual segmented C checker.
Counts are read from cert.2, never recomputed by PrimeWindow.count_at. -/
namespace RamanujanPV.CertificateMargin
open QuotientDemandCheck
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem list_certificate {start stop eLo eHi D : Nat} {rows : List RawFactoredCell}
    (cert : CompleteCertificate start stop (rows.map (fun r=>r.toCell eLo eHi)))
    (factored : ∀ r ∈ rows, r.A*r.Lu ≤ r.n*eLo)
    (margins : ∀ r ∈ rows, 2^20*(r.P^2+D) < r.A*r.Q) :
    ∀ x : ℝ, (start:ℝ) ≤ x → x < (stop:ℝ) → (D:ℝ) < gap x := by
  intro x hx hs
  obtain ⟨c,hc,hn,hm⟩ := cert.1.covers hx hs
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
  obtain ⟨numeric,counts,hexp,heLo,heHi,hlog⟩ := cert.2 _ (List.mem_map.mpr ⟨r,hr,rfl⟩)
  have hj : r.j*eHi ≤ r.n*2^60 := numeric.2.2.1
  change Nat.primeCounting (r.next-1)=r.P ∧ Nat.primeCounting r.j=r.Q at counts
  simp only [RawFactoredCell.toCell,Nat.cast_pow,Nat.cast_ofNat] at hexp heLo heHi
  have scaled : Real.log (r.n:ℝ)*(2:ℝ)^40 ≤ (r.Lu:ℝ) := by
    simp only [RawFactoredCell.toCell,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hlog
    norm_num at hlog ⊢
    nlinarith
  apply RecoveredMargin.factored_gap_lower hexp counts.1 counts.2 heLo heHi scaled hj
    (factored r hr) _ hn hm
  exact_mod_cast margins r hr

/-- The count proof retains exactly the provenance of the supplied certificate. -/
theorem array_certificate {start stop eLo eHi D count : Nat}
    {rows : Lean.RArray RawFactoredCell}
    (cert : CompleteCertificate start stop
      ((WindowCells.rawList rows count).map (fun r=>r.toCell eLo eHi)))
    (factored : ∀ i, i < count → (rows.get i).A*(rows.get i).Lu ≤ (rows.get i).n*eLo)
    (margins : allFrom (WindowMargin.check rows D) 0 count=true) :
    ∀ x : ℝ, (start:ℝ) ≤ x → x < (stop:ℝ) → (D:ℝ) < gap x := by
  apply list_certificate cert
  · intro r hr
    change r ∈ (List.range count).map rows.get at hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact factored i (List.mem_range.mp hi)
  · intro r hr
    change r ∈ (List.range count).map rows.get at hr
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
    exact of_decide_eq_true (allFrom_at count 0 margins i (by omega) (by have h:=List.mem_range.mp hi; omega))

/-- Pure fixed-point row checks supply only the A inequality; actual prime
counts still come solely from the caller's already completed certificate. -/
theorem checked_array_certificate {pBase qBase pCount qCount pValue qValue stop count D : Nat}
    {pEntries qEntries : Lean.RArray PrimeWindow.Entry} {rows : Lean.RArray RawFactoredCell}
    (cert : CompleteCertificate pBase stop
      ((WindowCells.rawList rows count).map (fun r=>r.toCell WindowCells.eLo WindowCells.eHi)))
    (checked : WindowCells.checkRows pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows=true)
    (margins : allFrom (WindowMargin.check rows D) 0 count=true) :
    ∀ x : ℝ, (pBase:ℝ) ≤ x → x < (stop:ℝ) → (D:ℝ) < gap x := by
  apply array_certificate cert _ margins
  intro i hi
  have parts : 0 < count ∧ allFrom
      (WindowCells.checkRow pBase qBase pCount qCount pValue qValue stop count pEntries qEntries rows) 0 count=true := by
    simpa [WindowCells.checkRows] using checked
  have spec := (WindowCells.checkRow_clauses (allFrom_at count 0 parts.2 i (by omega) (by omega))).1
  obtain ⟨pn,step,pend,qn,qend,pval,qval,lu,je,ac,rest⟩ := spec
  exact ac

#print axioms list_certificate
#print axioms array_certificate
#print axioms checked_array_certificate
end RamanujanPV.CertificateMargin
