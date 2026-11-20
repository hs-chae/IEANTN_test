/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveSlices
import RamanujanPV.PackedSievePrimitiveQWindow
import RamanujanPV.LocalCellsMillion.Data
namespace RamanujanPV.PackedSieveQQueries
open PackedSieveKernel PackedSieveByteCount PackedSieveSlices
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable def queries : List (Nat×Nat) := (List.range 285).map (fun i => 
  ((LocalCellsMillion.rows.get i).j-14111427770,
   (LocalCellsMillion.rows.get i).Q-632207037))
theorem checked : checkSlices PackedSievePrimitiveQWindow.bits 0 0 queries=true := by
  decide +kernel
theorem value (i : Nat) (hi : i<285) :
    lowCount ((LocalCellsMillion.rows.get i).j-14111427770)
      (primeBits 14111427771 367880)=(LocalCellsMillion.rows.get i).Q-632207037 := by
  let row : Nat × Nat := ((LocalCellsMillion.rows.get i).j-14111427770,
    (LocalCellsMillion.rows.get i).Q-632207037)
  have member : row ∈ queries := List.mem_map.mpr ⟨i,List.mem_range.mpr hi,rfl⟩
  have actual := checkSlices_from_zero (bits:=PackedSievePrimitiveQWindow.bits)
    (rows:=queries) checked row member
  calc
    lowCount ((LocalCellsMillion.rows.get i).j-14111427770) (primeBits 14111427771 367880) =
        lowCount ((LocalCellsMillion.rows.get i).j-14111427770) PackedSievePrimitiveQWindow.bits :=
      congrArg (lowCount ((LocalCellsMillion.rows.get i).j-14111427770)) PackedSievePrimitiveQWindow.packed_bits
    _ = (LocalCellsMillion.rows.get i).Q-632207037 := actual.symm

#print axioms checked
#print axioms value
end RamanujanPV.PackedSieveQQueries
