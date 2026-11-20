/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveSlices
import RamanujanPV.PackedSieveQQueries
import RamanujanPV.PackedSieveProvider
import RamanujanPV.PackedSievePrimitiveMaskMillion
import RamanujanPV.PackedSievePrimitiveQWindow
import RamanujanPV.LocalCellsMillion.Data
import RamanujanPV.PackedSieveAnchors
namespace RamanujanPV.PackedSieveQueries
open PackedSieveKernel PackedSieveByteCount PackedSievePrefix PackedSieveSlices
open PackedSieveProvider QuotientCCell WindowCells QuotientDemandCheck
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

noncomputable def pQueries : List (Nat×Nat) := (List.range 285).map (fun i =>
  ((LocalCellsMillion.rows.get i).next-1-38358837683,
   (LocalCellsMillion.rows.get i).P-1644673232))
noncomputable def qQueries : List (Nat × Nat) := PackedSieveQQueries.queries

theorem p_slices_checked : checkSlices PackedSievePrimitiveMaskMillion.bits 0 0 pQueries=true := by
  decide +kernel

theorem q_slices_checked : checkSlices PackedSievePrimitiveQWindow.bits 0 0 qQueries=true :=
  PackedSieveQQueries.checked

noncomputable def locationCheck (i : Nat) : Bool := let r:=LocalCellsMillion.rows.get i
  decide (38358837683≤r.next-1 ∧ r.next-1≤38359837683 ∧
    14111427770≤r.j ∧ r.j≤14111795650 ∧ 1644673232≤r.P ∧ 632207037≤r.Q)
theorem locations_checked : allFrom locationCheck 0 285=true := by decide +kernel

theorem p_value (i : Nat) (hi : i<285) :
    lowCount ((LocalCellsMillion.rows.get i).next-1-38358837683)
      (primeBits 38358837684 1000000)=(LocalCellsMillion.rows.get i).P-1644673232 := by
  let row : Nat × Nat := ((LocalCellsMillion.rows.get i).next-1-38358837683,
    (LocalCellsMillion.rows.get i).P-1644673232)
  have member : row ∈ pQueries := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have actual := checkSlices_from_zero (bits:=PackedSievePrimitiveMaskMillion.bits)
    (rows:=pQueries) p_slices_checked row member
  calc
    lowCount ((LocalCellsMillion.rows.get i).next-1-38358837683) (primeBits 38358837684 1000000) =
        lowCount ((LocalCellsMillion.rows.get i).next-1-38358837683) PackedSievePrimitiveMaskMillion.bits :=
      congrArg (lowCount ((LocalCellsMillion.rows.get i).next-1-38358837683)) PackedSievePrimitiveMaskMillion.packed_bits
    _ = (LocalCellsMillion.rows.get i).P-1644673232 := actual.symm

theorem q_value (i : Nat) (hi : i < 285) :
    lowCount ((LocalCellsMillion.rows.get i).j-14111427770)
      (primeBits 14111427771 367880)=(LocalCellsMillion.rows.get i).Q-632207037 :=
  PackedSieveQQueries.value i hi

theorem row_source_counts (i : Nat) (hi : i<285) :
    SourceExecution ((LocalCellsMillion.rows.get i).next-1) (LocalCellsMillion.rows.get i).P ∧
      SourceExecution (LocalCellsMillion.rows.get i).j (LocalCellsMillion.rows.get i).Q := by
  have bounds := allFrom_at 285 0 locations_checked i (by omega) (by omega)
  have clauses : 38358837683≤(LocalCellsMillion.rows.get i).next-1 ∧
      (LocalCellsMillion.rows.get i).next-1≤38359837683 ∧
      14111427770≤(LocalCellsMillion.rows.get i).j ∧
      (LocalCellsMillion.rows.get i).j≤14111795650 ∧
      1644673232≤(LocalCellsMillion.rows.get i).P ∧
      632207037≤(LocalCellsMillion.rows.get i).Q := by simpa [locationCheck] using bounds
  constructor
  · by_cases zero : (LocalCellsMillion.rows.get i).next-1=38358837683
    · have val:=p_value i hi
      simp only [zero,Nat.sub_self,PackedSieveByteCount.lowCount,Finset.range_zero,Finset.sum_empty] at val
      have output : (LocalCellsMillion.rows.get i).P=1644673232 := by omega
      rw [zero,output]
      exact PackedSieveAnchors.p_source
    · let offset := (LocalCellsMillion.rows.get i).next-1-38358837683
      have positive : 0<offset := by dsimp [offset];omega
      have provider := source_bound_provider (lo:=38358837684) (count:=1000000)
        PackedSieveAnchors.p_source (by decide) (by decide) (by decide) (by decide)
      have run := provider.2 (offset-1) (by dsimp [offset];omega)
      have succ : offset-1+1=offset := by omega
      have bytes : (offset-1+8)/8=(offset+7)/8 := by omega
      rw [succ,bytes,byteCount_prefix] at run
      have val:=p_value i hi
      have index : 38358837684+(offset-1)=(LocalCellsMillion.rows.get i).next-1 := by dsimp [offset];omega
      have output : 1644673232+lowCount offset (primeBits 38358837684 1000000)=
          (LocalCellsMillion.rows.get i).P := by dsimp [offset];rw [val];omega
      rw [index,output] at run
      exact run
  · by_cases zero : (LocalCellsMillion.rows.get i).j=14111427770
    · have val:=q_value i hi
      simp only [zero,Nat.sub_self,PackedSieveByteCount.lowCount,Finset.range_zero,Finset.sum_empty] at val
      have output : (LocalCellsMillion.rows.get i).Q=632207037 := by omega
      rw [zero,output]
      exact PackedSieveAnchors.q_source
    · let offset := (LocalCellsMillion.rows.get i).j-14111427770
      have positive : 0<offset := by dsimp [offset];omega
      have provider := source_bound_provider (lo:=14111427771) (count:=367880)
        PackedSieveAnchors.q_source (by decide) (by decide) (by decide) (by decide)
      have run := provider.2 (offset-1) (by dsimp [offset];omega)
      have succ : offset-1+1=offset := by omega
      have bytes : (offset-1+8)/8=(offset+7)/8 := by omega
      rw [succ,bytes,byteCount_prefix] at run
      have val:=q_value i hi
      have index : 14111427771+(offset-1)=(LocalCellsMillion.rows.get i).j := by dsimp [offset];omega
      have output : 632207037+lowCount offset (primeBits 14111427771 367880)=
          (LocalCellsMillion.rows.get i).Q := by dsimp [offset];rw [val];omega
      rw [index,output] at run
      exact run
#print axioms p_slices_checked
#print axioms q_slices_checked
#print axioms row_source_counts
end RamanujanPV.PackedSieveQueries
