/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import Mathlib

namespace ScopedC.NatArena
set_option autoImplicit false
set_option maxHeartbeats 0

/-!+This is the disclosed *generic pinned Lean runtime* boundary, not a proof of
the runtime's C implementation. Runtime Nat primitives may implement exact
arithmetic. No application evaluator, rational operation, Taylor routine,
integration loop or acceptance predicate is a primitive here.

An arena index names a logical object/reference provenance, not a claim that
physical pointers are distinct. In particular boxed small naturals and runtime
results may alias. The application must retain a live ownership token before
clearing a pool containing the original token. Refcounts are only an abstract
applicability contract; generic allocator and RC implementation are external.
-/

structure Arena where
  values : List Nat
  owners : Nat → Nat

def empty : Arena := ⟨[],fun _ => 0⟩
def Borrow (a : Arena) (slot value : Nat) : Prop :=
  a.values[slot]? = some value ∧ 0 < a.owners slot

def allocate (a : Arena) (value : Nat) : Nat × Arena :=
  (a.values.length,⟨a.values ++ [value],
    fun slot => if slot = a.values.length then 1 else a.owners slot⟩)

def retain (a : Arena) (slot : Nat) : Option Arena :=
  if slot < a.values.length ∧ 0 < a.owners slot then
    some {a with owners := fun i => if i = slot then a.owners i + 1 else a.owners i}
  else none

def release (a : Arena) (slot : Nat) : Option Arena :=
  if slot < a.values.length ∧ 0 < a.owners slot then
    some {a with owners := fun i => if i = slot then a.owners i - 1 else a.owners i}
  else none

def read (a : Arena) (slot : Nat) : Option Nat :=
  if 0 < a.owners slot then a.values[slot]? else none

inductive BinaryOp where
  | add | sub | mul | div | mod | gcd | shiftLeft | shiftRight
  deriving DecidableEq, Repr

def operation (op : BinaryOp) (a b : Nat) : Option Nat :=
  match op with
  | .add => some (a+b)
  | .sub => some (a-b)
  | .mul => some (a*b)
  | .div => if b = 0 then none else some (a/b)
  | .mod => if b = 0 then none else some (a%b)
  | .gcd => some (a.gcd b)
  | .shiftLeft => some (a <<< b)
  | .shiftRight => some (a >>> b)

/-- Both arguments are borrowed. The returned logical object owns one token.
The application's pool must account for that token; this rule never clears or
implicitly retains an application object. Division by zero is rejected even
though a total runtime implementation may have a convention there. -/
def binary (op : BinaryOp) (a : Arena) (left right : Nat) : Option (Nat × Arena) := do
  let x ← read a left
  let y ← read a right
  let result ← operation op x y
  pure (allocate a result)

def readCount (a : Arena) (refs : List Nat) : Nat → Nat :=
  fun i => a.owners i - refs.count i

/-- Mathematical summary of releasing exactly the tokens stored in a pool.
The C loop still needs its actual statement-execution proof; this is the
invariant it consumes, not an extra program-success hypothesis. -/
def clear (a : Arena) (refs : List Nat) : Arena :=
  {a with owners := readCount a refs}

def PoolOwned (a : Arena) (refs : List Nat) : Prop :=
  ∀ i, refs.count i ≤ a.owners i

theorem allocate_borrow (a : Arena) (n : Nat) :
    Borrow (allocate a n).2 (allocate a n).1 n := by
  simp [Borrow,allocate]

theorem read_of_borrow {a : Arena} {slot n : Nat} (h : Borrow a slot n) :
    read a slot = some n := by simp [read,h.2,h.1]

theorem retained_token_survives_clear {a : Arena} {refs : List Nat} {slot n : Nat}
    (value : a.values[slot]? = some n)
    (retained : refs.count slot < a.owners slot) :
    Borrow (clear a refs) slot n := by
  constructor
  · exact value
  · simp only [clear,readCount]
    omega

theorem clear_unrelated {a : Arena} {refs : List Nat} {slot : Nat}
    (absent : slot ∉ refs) : (clear a refs).owners slot = a.owners slot := by
  simp [clear,readCount,List.count_eq_zero.mpr absent]

theorem release_pool_cons (a : Arena) (first : Nat) (rest : List Nat) (i : Nat) :
    (clear a (first::rest)).owners i =
      (clear {a with owners := fun j => a.owners j - (if j = first then 1 else 0)} rest).owners i := by
  by_cases h : i = first
  · subst first
    simp [clear,readCount,Nat.sub_sub]
    omega
  · have h' : first ≠ i := Ne.symm h
    simp [clear,readCount,h,h']

/-- Writing a new owned token is allowed only inside the actual pool extent. -/
def register (capacity : Nat) (refs : List Nat) (slot : Nat) : Option (List Nat) :=
  if refs.length < capacity then some (refs ++ [slot]) else none

theorem register_extent {capacity : Nat} {refs : List Nat} {slot : Nat}
    (h : refs.length < capacity) :
    register capacity refs slot = some (refs ++ [slot]) ∧
    (refs ++ [slot]).length ≤ capacity := by
  simp only [register,h,↓reduceIte,List.length_append,List.length_singleton]
  constructor
  · trivial
  · omega

theorem zero_divisor_rejected : operation .div 7 0 = none := rfl

#print axioms allocate_borrow
#print axioms retained_token_survives_clear
#print axioms release_pool_cons
#print axioms register_extent
end ScopedC.NatArena
