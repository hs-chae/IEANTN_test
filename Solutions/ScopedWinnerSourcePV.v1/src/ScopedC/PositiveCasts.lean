/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatUnsignedCall
namespace ScopedC.PositiveCasts
open ScopedC.Machine ScopedC.PoolCalls ScopedC.NatWrapperCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem cast_N (cfg : Layout) (s : State) (fuel slot n : Nat)
    (live : NatArena.Borrow s.nats slot n) :
    castValue cfg s (fuel+1) "N" (.natObject slot)=some (.natObject slot) := by
  change (do let _ ← NatArena.read s.nats slot; pure (Value.natObject slot))=some (.natObject slot)
  rw [NatArena.read_of_borrow live]
  rfl

theorem cast_unsigned (s : State) (fuel n : Nat) (bound : n<2^32) :
    castValue Header.layout s (fuel+1) "unsigned" (unsigned32 n)=some (unsigned32 n) := by
  have range : Scalar.InRange ⟨false,32⟩ (n:Int) := by
    simp only [Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,Bool.false_eq_true,↓reduceIte]
    exact ⟨by omega,by exact_mod_cast Nat.zero_le n,by exact_mod_cast bound⟩
  change (do let x ← Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(n:Int)⟩
             pure (Value.integer x))=some (unsigned32 n)
  simp only [Scalar.cast]
  rw [Scalar.make_exact range]
  rfl

theorem fields {s : State} {slot n neg : Nat} (live : NatArena.Borrow s.nats slot n)
    (bound : neg<2^32) :
    ([ ("mag","N"),("neg","unsigned") ].zip [.natObject slot,unsigned32 neg]).mapM
      (fun item => castValue Header.layout s 99 item.1.2 item.2)=some [.natObject slot,unsigned32 neg] := by
  have cn := cast_N Header.layout s 98 slot n live
  have cu := cast_unsigned s 98 neg bound
  change (do
    let x ← castValue Header.layout s 99 "N" (.natObject slot)
    let y ← castValue Header.layout s 99 "unsigned" (unsigned32 neg)
    pure [x,y])=some [.natObject slot,unsigned32 neg]
  rw [cn,cu]
  rfl
end ScopedC.PositiveCasts
