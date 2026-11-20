/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveKernel

/-! A standalone proposed mask representation. This only reconstructs a natural
number from balanced chunks; it is not new source-first C program verification. -/
namespace RamanujanPV.PackedMaskEncodingCodec
set_option autoImplicit false

def assemble (width : Nat) : Lean.RArray Nat → Nat
  | .leaf value => value
  | .branch leftCount left right =>
      assemble width left ||| Nat.shiftLeft (assemble width right) (width*leftCount)

@[simp] theorem assemble_leaf (width value : Nat) :
    assemble width (.leaf value)=value := rfl

@[simp] theorem assemble_branch (width leftCount : Nat) (left right : Lean.RArray Nat) :
    assemble width (.branch leftCount left right)=
      assemble width left ||| Nat.shiftLeft (assemble width right) (width*leftCount) := rfl

#print axioms assemble_leaf
#print axioms assemble_branch
end RamanujanPV.PackedMaskEncodingCodec
