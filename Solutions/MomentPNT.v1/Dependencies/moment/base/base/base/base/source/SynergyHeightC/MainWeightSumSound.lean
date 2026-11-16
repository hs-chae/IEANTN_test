/- Sound accumulation of exact integer interval sums, with abstract cell data. -/
import SynergyHeightC.MainWeightReal
import SynergyHeightC.MainWeightFold
namespace SynergyHeightC.MainWeightModel
open ScopedNumerical SynergyBasis
set_option autoImplicit false
set_option maxHeartbeats 200000

theorem fold_real_sound (get : Nat → Option ProofBox) (value : Nat → ℝ)
    (indices : List Nat) {start finish : ProofBox} {initial : ℝ}
    (hs : RealBox.Contains 128 start initial)
    (hc : ∀ i ∈ indices, ∀ b, get i=some b → RealBox.Contains 128 b (value i))
    (run : indices.foldlM (addCell get) start=some finish) :
    RealBox.Contains 128 finish (initial+(indices.map value).sum) := by
  induction indices generalizing start initial with
  | nil =>
      have he : start=finish := Option.some.inj run
      subst finish
      simpa using hs
  | cons i tail ih =>
      cases hg : get i with
      | none => simp [List.foldlM,addCell,hg] at run
      | some b =>
          have hstep := RealBox.add_sound hs (hc i (by simp) b hg)
          have htail : ∀ j ∈ tail, ∀ out,
              get j=some out → RealBox.Contains 128 out (value j) := by
            intro j hj out hget
            exact hc j (List.mem_cons_of_mem i hj) out hget
          have hrun : tail.foldlM (addCell get) (ProofBox.add start b)=some finish := by
            simpa only [List.foldlM_cons,addCell,hg,Bind.bind,Option.bind,Pure.pure] using run
          have hr := ih hstep htail hrun
          simpa only [List.map_cons,List.sum_cons,_root_.add_assoc] using hr

theorem list_range_sum (value : Nat → ℝ) (n : Nat) :
    ((List.range n).map value).sum=∑ i ∈ Finset.range n,value i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ,List.map_append,List.sum_append,ih,Finset.sum_range_succ]
      simp

theorem block_real_sum_sound (lo count : Nat) (value : Nat → ℝ)
    (hc : ∀ j < count, ∀ b, cell (lo+j)=some b → RealBox.Contains 128 b (value (lo+j)))
    {out : ProofBox} (run : block lo count=some out) :
    RealBox.Contains 128 out (∑ j ∈ Finset.range count,value (lo+j)) := by
  have hs : RealBox.Contains 128 (⟨0,0⟩ : ProofBox) (0 : ℝ) := by
    simp [RealBox.Contains]
  have hr := fold_real_sound (fun j=>cell (lo+j)) (fun j=>value (lo+j))
    (List.range count) hs (fun j hj b hb=>hc j (List.mem_range.mp hj) b hb) run
  simpa only [list_range_sum,_root_.zero_add] using hr

theorem block_real_sum_upper (lo count : Nat) (value : Nat → ℝ)
    (hc : ∀ j < count, ∀ b, cell (lo+j)=some b → RealBox.Contains 128 b (value (lo+j)))
    {out : ProofBox} (run : block lo count=some out) :
    (∑ j ∈ Finset.range count,value (lo+j)) ≤ realWord out.hi := by
  have hr := (block_real_sum_sound lo count value hc run).2
  exact (le_div_iff₀ (RealBox.scale_real_pos 128)).mpr hr

#print axioms fold_real_sound
#print axioms block_real_sum_sound
#print axioms block_real_sum_upper
end SynergyHeightC.MainWeightModel
