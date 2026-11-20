/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveKernel
namespace RamanujanPV.PackedSieveFold
set_option autoImplicit false

theorem fold_or_bit (xs : List Nat) (f : Nat→Nat) (seed bit : Nat) :
    (xs.foldl (fun bits j=>bits ||| f j) seed).testBit bit=true ↔
      seed.testBit bit=true ∨ ∃j∈xs,(f j).testBit bit=true := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,ih,Nat.testBit_lor,Bool.or_eq_true,List.mem_cons]
    aesop

theorem fold_filtered_bit (xs : List Nat) (f : Nat→Nat) (skip : Nat→Bool)
    (seed bit : Nat) :
    (xs.foldl (fun bits j=>if skip j then bits else bits ||| f j) seed).testBit bit=true ↔
      seed.testBit bit=true ∨ ∃j∈xs,skip j=false ∧ (f j).testBit bit=true := by
  induction xs generalizing seed with
  | nil => simp
  | cons a xs ih =>
    cases h : skip a <;> simp only [List.foldl_cons,h,Bool.false_eq_true,ite_false,
      ite_true,ih,Nat.testBit_lor,Bool.or_eq_true,List.mem_cons] <;> aesop

#print axioms fold_or_bit
#print axioms fold_filtered_bit
end RamanujanPV.PackedSieveFold
