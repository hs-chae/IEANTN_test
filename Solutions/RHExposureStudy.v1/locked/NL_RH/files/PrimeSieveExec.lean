import Std.Data.HashMap
import Init.Data.Nat.Sqrt

/-! The actual executable quotient sieve, with no Mathlib runtime dependency.
Theorems about its state and output are in PrimeCountProgram.lean. -/
namespace LocalPrimeSieve

def digits (n : Nat) : List Nat :=
  List.range (n.sqrt+1) ++ (List.range (n/(n.sqrt+1))).map (fun i => n/(i+1))

def keys (n : Nat) : List Nat := (digits n).mergeSort (fun a b => decide (b ≤ a))

abbrev Table := Std.HashMap Nat Nat
def get (t : Table) (k : Nat) : Nat := t.getD k 0

def initialise : List Nat → Table → Table
  | [], t => t
  | v :: vs, t => initialise vs (t.insert v (v-1))

def pass (p : Nat) : List Nat → Table → Table
  | [], t => t
  | v::vs, t =>
    if p*p ≤ v then
      pass p vs (t.insert v (get t v - (get t (v/p) - get t (p-1))))
    else t

def loop (l : List Nat) (p : Nat) : Nat → Table → Table
  | 0,t => t
  | fuel+1,t =>
    loop l (p+1) fuel
      (if get t (p-1) < get t p then pass p l t else t)

/-- The actual executable sparse quotient sieve. -/
def count (n : Nat) : Nat :=
  if n<2 then 0 else
    let l := keys n
    get (loop l 2 (n.sqrt-1) (initialise l ∅)) n

end LocalPrimeSieve
