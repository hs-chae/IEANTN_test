/- UInt64 source conversion and the specified eight little-endian words.
The actual shift/store loop must separately establish these array contents. -/
import SynergyHeightC.EmitUFrames
namespace SynergyHeightC.EmitUWord64
open ScopedC ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def type : Scalar.IntType := ⟨false,64⟩
def value (n : Int) : Value := .integer ⟨type,n⟩
def part (x : Int) (i : Nat) : Int := (x / (2^(64*i):Int)) % (2^64:Int)
def parts (x : Int) : List Int := (List.range 8).map (part x)
def cells (x : Int) : List (Option Value) := (parts x).map (fun n=>some (value n))

theorem part_range (x : Int) (i : Nat) : 0≤part x i ∧ part x i<2^64 := by
  exact ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩

theorem part_cast_nat (x : Int) (i : Nat) : ((part x i).toNat:Int)=part x i :=
  Int.toNat_of_nonneg (part_range x i).1

theorem cast_value (s : State) (z : Int) :
    Machine.castValue SynergyC.Header.layout s 100 "uint64_t" (SynergyC.Word512.value z)=
      some (value (z % (2^64:Int))) := by rfl

theorem cells_length (x : Int) : (cells x).length=8 := by simp [cells,parts]

theorem cast_shift_part (s : State) (x : Int) (i : Nat) :
    Machine.castValue SynergyC.Header.layout s 100 "uint64_t"
      (SynergyC.Word512.value (x/(2^(64*i):Int)))=some (value (part x i)) :=
  cast_value s _

#print axioms part_range
#print axioms part_cast_nat
#print axioms cast_value
#print axioms cells_length
#print axioms cast_shift_part
end SynergyHeightC.EmitUWord64
