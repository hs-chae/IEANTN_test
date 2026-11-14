/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.NatWrapperTemplate

namespace ScopedC.NatWrapperCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls ScopedC.PoolCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem na_call (code : List Function) (installed : Generated.f_na ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 2 "na" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n+m)) := by
  exact binary_call code Generated.f_na "lean_nat_add" .add installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (rfl)

theorem ns_call (code : List Function) (installed : Generated.f_ns ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 2 "ns" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n-m)) := by
  exact binary_call code Generated.f_ns "lean_nat_sub" .sub installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (rfl)

theorem nm_call (code : List Function) (installed : Generated.f_nm ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 2 "nm" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n*m)) := by
  exact binary_call code Generated.f_nm "lean_nat_mul" .mul installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (rfl)

theorem nd_call (code : List Function) (installed : Generated.f_nd ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) (nonzero : m ≠ 0) :
    SourceCall Header.layout code 2 "nd" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n/m)) := by
  exact binary_call code Generated.f_nd "lean_nat_div" .div installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (by simp [NatArena.operation,nonzero])

theorem nr_call (code : List Function) (installed : Generated.f_nr ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) (nonzero : m ≠ 0) :
    SourceCall Header.layout code 2 "nr" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n%m)) := by
  exact binary_call code Generated.f_nr "lean_nat_mod" .mod installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (by simp [NatArena.operation,nonzero])

theorem ng_call (code : List Function) (installed : Generated.f_ng ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 2 "ng" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n.gcd m)) := by
  exact binary_call code Generated.f_ng "lean_nat_gcd" .gcd installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (rfl)

theorem nl_call (code : List Function) (installed : Generated.f_nl ∈ code)
    (keepInstalled : Generated.f_keep ∈ code)
    {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high a b n m : Nat}
    (context : GenericPoolContext l s cells top high) (room : top < capacity)
    (ha : NatArena.Borrow s.nats a n) (hb : NatArena.Borrow s.nats b m) :
    SourceCall Header.layout code 2 "nl" [.natObject a,.natObject b] s
      (.natObject s.nats.values.length) (binaryResult l s cells top high (n <<< m)) := by
  exact binary_call code Generated.f_nl "lean_nat_shiftl" .shiftLeft installed keepInstalled
    rfl rfl rfl (by decide +kernel) context room ha hb (rfl)

end ScopedC.NatWrapperCalls
