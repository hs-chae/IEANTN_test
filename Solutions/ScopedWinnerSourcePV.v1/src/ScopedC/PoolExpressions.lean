/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.PoolMemory

namespace ScopedC.PoolCalls
open ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 10000

 theorem context_env {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (env : Env) :
    GenericPoolContext l {s with env:=env} cells top high := by
  exact ⟨h.global_pool,h.global_top,h.global_high,h.pool_read,h.top_read,h.high_read,
    h.extent,h.high_range,h.top_range⟩
 theorem context_nats {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (nats : NatArena.Arena) :
    GenericPoolContext l {s with nats:=nats} cells top high := by
  exact ⟨h.global_pool,h.global_top,h.global_high,h.pool_read,h.top_read,h.high_read,
    h.extent,h.high_range,h.top_range⟩
 theorem context_append {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high : Nat} (h : GenericPoolContext l s cells top high) (extra : List Object) :
    GenericPoolContext l {s with heap:=s.heap++extra} cells top high := by
  constructor
  · exact h.global_pool
  · exact h.global_top
  · exact h.global_high
  · rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp h.pool_read).choose)];exact h.pool_read
  · rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp h.top_read).choose)];exact h.top_read
  · rw [List.getElem?_append_left ((List.getElem?_eq_some_iff.mp h.high_read).choose)];exact h.high_read
  · exact h.extent
  · exact h.high_range
  · exact h.top_range

 theorem eval_top {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    evalExpr Header.layout call (fuel+1) s (.var "poolTop") = some (word top,s) := by
  rw [evalExpr]
  simp [getVar,free.2.1,h.global_top,h.top_read,counterObject,Machine.read,
    nested,initialized,word]
 theorem eval_high {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    evalExpr Header.layout call (fuel+1) s (.var "poolHigh") = some (word high,s) := by
  rw [evalExpr]
  simp [getVar,free.2.2,h.global_high,h.high_read,counterObject,Machine.read,
    nested,initialized,word]
 theorem eval_pool {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    evalExpr Header.layout call (fuel+1) s (.var "pool") = some (.pointer ⟨l.pool,0,[]⟩ true,s) := by
  rw [evalExpr]
  simp [getVar,free.1,h.global_pool,h.pool_read,poolObject]

 theorem lvalue_top {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    evalLValue Header.layout call (fuel+1) s (.var "poolTop") = some (⟨l.top,0,[]⟩,true,s) := by
  rw [evalLValue]
  simp [getVar,free.2.1,h.global_top,h.top_read,counterObject]
 theorem lvalue_high {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) :
    evalLValue Header.layout call (fuel+1) s (.var "poolHigh") = some (⟨l.high,0,[]⟩,true,s) := by
  rw [evalLValue]
  simp [getVar,free.2.2,h.global_high,h.high_read,counterObject]
 theorem lvalue_pool_top {l : PoolLayout} {s : State} {cells : List (Option Value)}
    {top high fuel : Nat} (call : Call) (h : GenericPoolContext l s cells top high)
    (free : LocalsFree s) (ht : top < capacity) :
    evalLValue Header.layout call (fuel+2) s (.index (.var "pool") (.var "poolTop")) =
      some (⟨l.pool,top,[]⟩,true,s) := by
  have hin : top < cells.length := by rw [h.extent];exact ht
  rw [evalLValue,eval_pool call h free]
  simp [eval_top call h free,asNat,word,addressType,h.pool_read,poolObject,hin,typeAt]

 theorem eval_assign {s mid after : State} {e lhs : Expr} {v : Value}
    {addr : Address} {writable : Bool} {fuel : Nat} (call : Call)
    (rhs : evalExpr Header.layout call fuel s e = some (v,mid))
    (left : evalLValue Header.layout call fuel mid lhs = some (addr,writable,mid))
    (store : write Header.layout mid addr writable v = some (v,after)) :
    evalExpr Header.layout call (fuel+1) s (.binary "=" lhs e) = some (v,after) := by
  rw [evalExpr,rhs]
  simp only [bind,Option.bind]
  rw [left]
  exact store

 theorem eval_call_one {s mid after : State} {e : Expr} {v out : Value}
    {name : String} {fuel : Nat} (call : Call)
    (arg : evalExpr Header.layout call fuel s e = some (v,mid))
    (answer : call name [v] mid = some (out,after)) :
    evalExpr Header.layout call (fuel+1) s (.call (.var name) [e]) = some (out,after) := by
  rw [evalExpr]
  simp [List.foldlM,arg,answer]

 theorem scalar_u32_cast (n : Nat) (hn : n < 2^32) :
    Scalar.cast ⟨false,32⟩ ⟨⟨false,32⟩,(n:Int)⟩ = some ⟨⟨false,32⟩,(n:Int)⟩ := by
  apply Scalar.make_exact
  simp only [Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus, Bool.false_eq_true,↓reduceIte]
  constructor
  · omega
  · constructor
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast hn

 theorem u32_range (n : Nat) (hn : n < 2^32) : Scalar.InRange ⟨false,32⟩ (n:Int) := by
  simp only [Scalar.InRange,Scalar.lower,Scalar.upper,Scalar.modulus,Bool.false_eq_true,↓reduceIte]
  constructor
  · omega
  · constructor
    · exact_mod_cast Nat.zero_le n
    · exact_mod_cast hn

 theorem binary_cap (s : State) (n : Nat) (hn : n < capacity) :
    binaryValue Header.layout s ">=" (word n) (.integer ⟨⟨true,32⟩,4000000⟩) =
      some (boolean Header.layout false) := by
  have h32 : n < 2^32 := by dsimp [capacity] at hn;omega
  have hi : (n:Int) < 4000000 := by exact_mod_cast hn
  simp [binaryValue,word,Scalar.binary,Scalar.common,Scalar.promote,Scalar.cast,
    Scalar.make,Scalar.modulus,Int.emod_eq_of_lt (Int.natCast_nonneg n) (show (n:Int) < 2^32 by exact_mod_cast h32),
    hi.not_ge,Scalar.boolean,Scalar.truth,boolean, u32_range n h32,
    show Scalar.InRange ⟨true,32⟩ 4000000 by decide +kernel]
  rw [Int.emod_eq_of_lt (Int.natCast_nonneg n) (by omega)]
  exact hi

 theorem binary_lt (s : State) (n k : Nat) (hn : n < 2^32) (hk : k < 2^32) :
    binaryValue Header.layout s "<" (word n) (word k) =
      some (boolean Header.layout (decide (n < k))) := by
  simp [binaryValue,word,Scalar.binary,Scalar.common,Scalar.promote,scalar_u32_cast n hn,
    scalar_u32_cast k hk,Scalar.boolean,Scalar.truth,boolean,u32_range n hn,u32_range k hk]
    <;> split_ifs <;> (first | rfl | omega)

 theorem binary_gt (s : State) (n k : Nat) (hn : n < 2^32) (hk : k < 2^32) :
    binaryValue Header.layout s ">" (word n) (word k) =
      some (boolean Header.layout (decide (n > k))) := by
  simp [binaryValue,word,Scalar.binary,Scalar.common,Scalar.promote,scalar_u32_cast n hn,
    scalar_u32_cast k hk,Scalar.boolean,Scalar.truth,boolean,u32_range n hn,u32_range k hk]
    <;> split_ifs <;> (first | rfl | omega)

 theorem binary_add_one (s : State) (n : Nat) (hn : n+1 < 2^32) :
    binaryValue Header.layout s "+" (word n) (.integer ⟨⟨true,32⟩,1⟩) = some (word (n+1)) := by
  have hn0 : (n:Int) < 2^32 := by omega
  have hn1 : (n:Int)+1 < 2^32 := by exact_mod_cast hn
  simp [binaryValue,word,Scalar.binary,Scalar.common,Scalar.promote,Scalar.cast,
    Scalar.make,Scalar.modulus,Int.emod_eq_of_lt (Int.natCast_nonneg n) hn0,
    Int.emod_eq_of_lt (by omega : (0:Int) ≤ (n:Int)+1) hn1, u32_range n (by omega),
    show Scalar.InRange ⟨true,32⟩ 1 by decide +kernel]
  exact Int.emod_eq_of_lt (by omega) (by omega)

 theorem binary_sub_one (s : State) (n : Nat) (hp : 0 < n) (hn : n < 2^32) :
    binaryValue Header.layout s "-" (word n) (.integer ⟨⟨true,32⟩,1⟩) = some (word (n-1)) := by
  have hn0 : (n:Int) < 2^32 := by exact_mod_cast hn
  have hn1 : (n:Int)-1 < 2^32 := by omega
  have hn2 : (0:Int) ≤ (n:Int)-1 := by omega
  simp [binaryValue,word,Scalar.binary,Scalar.common,Scalar.promote,Scalar.cast,
    Scalar.make,Scalar.modulus,Int.emod_eq_of_lt (Int.natCast_nonneg n) hn0,
    Int.emod_eq_of_lt hn2 hn1,Int.natCast_sub (by omega : 1 ≤ n),u32_range n hn,
    show Scalar.InRange ⟨true,32⟩ 1 by decide +kernel]
  exact Int.emod_eq_of_lt (by omega) (by omega)

end ScopedC.PoolCalls
