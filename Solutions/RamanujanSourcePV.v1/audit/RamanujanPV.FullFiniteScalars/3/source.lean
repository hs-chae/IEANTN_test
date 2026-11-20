/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.WindowCells

/-! Exact scalar/enclosure/adjacency certificates for the ORIGINAL full finite
seven-word dataset. These are mathematical kernel certificates, not C source PV.
No prime-count value is established by these checks. -/
namespace RamanujanPV.FullFiniteScalars
open QuotientDemandCheck AnalyticTransition WindowCells
set_option autoImplicit false
set_option maxHeartbeats 0

structure Entry where
  row : RawFactoredCell
  k : Nat

def Spec (e : Entry) : Prop :=
  let r:=e.row
  38358837683 ≤ r.n ∧ r.n < r.next ∧ r.next ≤ 1490000000001 ∧
  0 < r.Lu ∧ r.j*eHi ≤ r.n*2^60 ∧ r.A*r.Lu ≤ r.n*eLo ∧
  2^20*r.P^2 < r.A*r.Q ∧ 2^e.k ≤ r.n ∧ r.n < 2*(2^e.k) ∧
  r.Lu=binaryLogUpper r.n (2^e.k) e.k

noncomputable instance specDecidable (e : Entry) : Decidable (Spec e) := by
  unfold Spec
  infer_instance

noncomputable def checkOne (start stop count : Nat) (rows : Lean.RArray Entry) (i : Nat) : Bool :=
  @decide (Spec (rows.get i)) (specDecidable _) &&
  decide (i=0 → (rows.get i).row.n=start) &&
  decide (if i+1 < count then (rows.get i).row.next=(rows.get (i+1)).row.n
    else (rows.get i).row.next=stop)

noncomputable def rawRows (rows : Lean.RArray Entry) (count : Nat) : List RawFactoredCell :=
  (List.range count).map (fun i=>(rows.get i).row)

lemma clauses {start stop count i : Nat} {rows : Lean.RArray Entry}
    (h : checkOne start stop count rows i=true) :
    Spec (rows.get i) ∧ (i=0 → (rows.get i).row.n=start) ∧
    (if i+1 < count then (rows.get i).row.next=(rows.get (i+1)).row.n
      else (rows.get i).row.next=stop) := by
  dsimp only [checkOne] at h
  have hs : decide (Spec (rows.get i))=true ∧
      decide (i=0 → (rows.get i).row.n=start)=true ∧
      decide (if i+1 < count then (rows.get i).row.next=(rows.get (i+1)).row.n
        else (rows.get i).row.next=stop)=true := by
    simpa only [Bool.and_eq_true,and_assoc] using h
  exact ⟨of_decide_eq_true hs.1,of_decide_eq_true hs.2.1,of_decide_eq_true hs.2.2⟩

lemma scalar_sound {e : Entry} (h : Spec e) :
    (e.row.toCell eLo eHi).FixedPredicate ∧ (e.row.toCell eLo eHi).Enclosures := by
  obtain ⟨low,step,upper,lu,je,ac,strict,lo,hi,logval⟩ := h
  have he := finite_e_enclosure
  rw [finiteELow_value] at he
  have helo : (eLo:ℝ) ≤ Real.exp 1*(2:ℝ)^60 :=
    (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp he.1
  have hehi : Real.exp 1*(2:ℝ)^60 ≤ (eHi:ℝ) :=
    (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^60)).mp he.2
  have hl := binaryLogUpper_sound (n:=e.row.n) (two:=2^e.k) (k:=e.k) rfl lo hi
  rw [←logval] at hl
  have scaled := (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^40)).mp hl
  have nlow : (38358837683:ℝ) ≤ e.row.n := by exact_mod_cast low
  have hn : Real.exp 1 ≤ (e.row.n:ℝ) := by linarith [Real.exp_one_lt_d9]
  exact ⟨e.row.toCell_fixedPredicate eLo eHi step lu je ac strict,
    e.row.toCell_enclosures eLo eHi hn helo hehi scaled⟩

/-- Every checked row has real enclosures and the strict predicate; the exact
chain covers every real point. This proves NO unverified prime-count fact. -/
theorem checked_block {start stop count : Nat} {rows : Lean.RArray Entry}
    (positive : 0 < count)
    (checked : allFrom (checkOne start stop count rows) 0 count=true) :
    RawCellChain start stop (rawRows rows count) ∧
      ∀ r ∈ rawRows rows count, (r.toCell eLo eHi).FixedPredicate ∧
        (r.toCell eLo eHi).Enclosures := by
  have each : ∀ i, i < count → Spec (rows.get i) ∧
      (i=0 → (rows.get i).row.n=start) ∧
      (if i+1 < count then (rows.get i).row.next=(rows.get (i+1)).row.n
        else (rows.get i).row.next=stop) := by
    intro i hi
    exact clauses (allFrom_at count 0 checked i (by omega) (by omega))
  let extended : Nat → RawFactoredCell := fun i=>if i < count then (rows.get i).row else boundaryRow stop
  have strict : ∀ i, 0 ≤ i → i < 0+count → (extended i).n < (extended i).next := by
    intro i low hi
    have bound : i < count := by omega
    simpa [extended,bound] using (each i bound).1.2.1
  have adjacent : ∀ i, 0 ≤ i → i < 0+count → (extended i).next=(extended (i+1)).n := by
    intro i low hi
    have bound : i < count := by omega
    have h := (each i bound).2.2
    by_cases next : i+1 < count
    · rw [if_pos next] at h
      simpa [extended,bound,next] using h
    · rw [if_neg next] at h
      simpa [extended,bound,next,boundaryRow] using h
  have chain := raw_chain_range extended count 0 strict adjacent
  have listEq : (List.range' 0 count).map extended=rawRows rows count := by
    unfold rawRows
    rw [List.range_eq_range']
    apply List.map_congr_left
    intro i hi
    have bound : i < count := by simpa using hi
    simp [extended,bound]
  rw [listEq] at chain
  have first : (extended 0).n=start := by simpa [extended,positive] using (each 0 positive).2.1 rfl
  have last : (extended (0+count)).n=stop := by simp [extended,boundaryRow]
  rw [first,last] at chain
  refine ⟨chain,?_⟩
  intro r hr
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hr
  exact scalar_sound (each i (List.mem_range.mp hi)).1

/-- A scalar certificate intentionally has no prime-count correctness field. -/
def ScalarCertificate (start stop : Nat) (rows : List RawFactoredCell) : Prop :=
  RawCellChain start stop rows ∧ ∀ r ∈ rows,
    (r.toCell eLo eHi).FixedPredicate ∧ (r.toCell eLo eHi).Enclosures

lemma append_chain {a b c : Nat} {xs ys : List RawFactoredCell}
    (left : RawCellChain a b xs) (right : RawCellChain b c ys) :
    RawCellChain a c (xs++ys) := by
  induction left with
  | nil n => simpa using right
  | cons row step rest ih => simpa using RawCellChain.cons row step ih

theorem append_certificate {a b c : Nat} {xs ys : List RawFactoredCell}
    (left : ScalarCertificate a b xs) (right : ScalarCertificate b c ys) :
    ScalarCertificate a c (xs++ys) := by
  refine ⟨append_chain left.1 right.1,?_⟩
  intro row member
  rcases List.mem_append.mp member with h|h
  · exact left.2 row h
  · exact right.2 row h

/-- Only actual missing count facts can turn this scalar witness into the
original complete mathematical certificate. This theorem does not supply them. -/
theorem complete_from_counts {start stop : Nat} {rows : List RawFactoredCell}
    (scalars : ScalarCertificate start stop rows)
    (counts : ∀ r ∈ rows, Nat.primeCounting (r.next-1)=r.P ∧ Nat.primeCounting r.j=r.Q) :
    CompleteCertificate start stop (rows.map (fun r=>r.toCell eLo eHi)) := by
  refine ⟨scalars.1.toCellChain eLo eHi,?_⟩
  intro cell member
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp member
  exact ⟨(scalars.2 r hr).1,r.toCell_counts eLo eHi (counts r hr).1 (counts r hr).2,
    (scalars.2 r hr).2⟩

#print axioms append_certificate
#print axioms complete_from_counts
#print axioms scalar_sound
#print axioms checked_block
end RamanujanPV.FullFiniteScalars
