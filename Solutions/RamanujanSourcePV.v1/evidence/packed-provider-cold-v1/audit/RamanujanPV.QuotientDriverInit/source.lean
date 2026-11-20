/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientDriverSource
import RamanujanPV.QuotientCMachine

/-! Application-owned static initialization of the source-bound driver.
No initial table contents, Owned predicate, or expected count is assumed.
The generic rule for a C static-storage array creates its actual declared
number of zero uint64 words. The compiler/linker must associate the two source
objects with addresses satisfying the explicit layout contract. Complete
counter execution and the fwrite/fflush world remain separate obligations. -/
namespace RamanujanPV.QuotientDriverInit
open QuotientDriverSource QuotientCMachine
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 2000000

def emptyHeap : Heap := fun _ => none

def zeroBlock (array : StaticArray) : Block :=
  ⟨array.count, fun _ => 0⟩

def storeArray (heap : Heap) (base : Nat) (array : StaticArray) : Heap :=
  Function.update heap base (some (zeroBlock array))

/-- Source-independent static-array allocation and zero initialization.
The address choice is explicit; disjointness and byte bounds are checked before
the source-owned array is installed. No rule specifies a desired count output. -/
inductive StaticInit : List StaticArray → List Nat → Heap → Heap → Prop
  | nil (heap : Heap) : StaticInit [] [] heap heap
  | cons {array arrays base bases heap next final}
      (positive : 0 < array.count)
      (aligned : base % 8 = 0)
      (bounded : base + 8 * array.count ≤ modulus)
      (fresh : heap base = none)
      (apart : ∀ address block, heap address = some block →
        base + 8 * array.count ≤ address ∨ address + 8 * block.extent ≤ base)
      (allocated : next = storeArray heap base array)
      (rest : StaticInit arrays bases next final) :
      StaticInit (array :: arrays) (base :: bases) heap final

theorem empty_owned : Owned emptyHeap := by
  constructor <;> simp [emptyHeap]

theorem storeArray_owned {heap : Heap} {base : Nat} {array : StaticArray}
    (owned : Owned heap) (aligned : base % 8 = 0)
    (bounded : base + 8 * array.count ≤ modulus)
    (apart : ∀ address block, heap address = some block →
      base + 8 * array.count ≤ address ∨ address + 8 * block.extent ≤ base) :
    Owned (storeArray heap base array) := by
  constructor
  · intro address block hblock
    by_cases h : address = base
    · subst address
      have hb : block = zeroBlock array := by simpa [storeArray] using hblock.symm
      subst block
      exact ⟨aligned, bounded⟩
    · exact owned.1 address block (by simpa [storeArray, Function.update_of_ne h] using hblock)
  · intro a b A B hA hB hab
    by_cases ha : a = base
    · subst a
      have hB0 : heap b = some B := by
        simpa [storeArray, Function.update_of_ne (Ne.symm hab)] using hB
      have hA0 : A = zeroBlock array := by simpa [storeArray] using hA.symm
      subst A
      exact apart b B hB0
    · by_cases hb : b = base
      · subst b
        have hA0 : heap a = some A := by simpa [storeArray, Function.update_of_ne ha] using hA
        have hB0 : B = zeroBlock array := by simpa [storeArray] using hB.symm
        subst B
        exact (apart a A hA0).symm
      · apply owned.2 a b A B
        · simpa [storeArray, Function.update_of_ne ha] using hA
        · simpa [storeArray, Function.update_of_ne hb] using hB
        · exact hab

theorem StaticInit.preserves_owned {arrays : List StaticArray} {bases : List Nat}
    {heap final : Heap} (run : StaticInit arrays bases heap final) (owned : Owned heap) :
    Owned final := by
  induction run with
  | nil => exact owned
  | cons positive aligned bounded fresh apart allocated rest ih =>
      apply ih
      rw [allocated]
      exact storeArray_owned owned aligned bounded apart

/-- Only storage layout is supplied by the compiler/linker ABI. Initial array
contents and their mathematical representation are constructed below from the
actual source declarations. These fields do not assert a successful program. -/
structure Layout where
  smallBase : Nat
  largeBase : Nat
  smallAligned : smallBase % 8 = 0
  largeAligned : largeBase % 8 = 0
  smallBounded : smallBase + 8 * capacity ≤ modulus
  largeBounded : largeBase + 8 * capacity ≤ modulus
  disjoint : smallBase + 8 * capacity ≤ largeBase ∨
    largeBase + 8 * capacity ≤ smallBase

theorem Layout.distinct (layout : Layout) : layout.smallBase ≠ layout.largeBase := by
  intro h
  have hc : 0 < capacity := by norm_num [capacity]
  rcases layout.disjoint with hleft | hright <;> omega

def smallArray : StaticArray := ⟨"rpc_small", .uint64, capacity⟩
def largeArray : StaticArray := ⟨"rpc_large", .uint64, capacity⟩

def initializedHeap (layout : Layout) : Heap :=
  storeArray (storeArray emptyHeap layout.smallBase smallArray) layout.largeBase largeArray

theorem source_static_initialization (layout : Layout) :
    StaticInit program.globals [layout.smallBase, layout.largeBase]
      emptyHeap (initializedHeap layout) := by
  apply StaticInit.cons (by norm_num [smallArray, capacity])
      layout.smallAligned layout.smallBounded (by rfl) (by simp [emptyHeap]) rfl
  apply StaticInit.cons (by norm_num [largeArray, capacity])
      layout.largeAligned layout.largeBounded
  · simp [storeArray, emptyHeap, layout.distinct.symm]
  · intro address block hblock
    by_cases h : address = layout.smallBase
    · subst address
      have hb : block = zeroBlock smallArray := by simpa [storeArray, smallArray] using hblock.symm
      subst block
      exact layout.disjoint.symm
    · simp [storeArray, Function.update_of_ne h, emptyHeap] at hblock
  · rfl
  · exact StaticInit.nil _

theorem initialized_owned (layout : Layout) : Owned (initializedHeap layout) :=
  (source_static_initialization layout).preserves_owned empty_owned

theorem initialized_small (layout : Layout) :
    initializedHeap layout layout.smallBase = some (zeroBlock smallArray) := by
  simp [initializedHeap, storeArray, layout.distinct]

theorem initialized_large (layout : Layout) :
    initializedHeap layout layout.largeBase = some (zeroBlock largeArray) := by
  simp [initializedHeap, storeArray]

theorem initialized_word_zero (layout : Layout) {i : Nat} (hi : i < capacity) :
    read (initializedHeap layout) layout.smallBase i = some (.u64 0) ∧
    read (initializedHeap layout) layout.largeBase i = some (.u64 0) := by
  constructor
  · apply read_of_block (initialized_small layout) layout.smallAligned hi
    · have h := layout.smallBounded
      have hc : (zeroBlock smallArray).extent = capacity := rfl
      omega
    · norm_num [zeroBlock, modulus]
  · apply read_of_block (initialized_large layout) layout.largeAligned hi
    · have h := layout.largeBounded
      omega
    · norm_num [zeroBlock, modulus]

def canonicalLayout : Layout where
  smallBase := 8
  largeBase := 12000008
  smallAligned := by norm_num
  largeAligned := by norm_num
  smallBounded := by norm_num [capacity, modulus]
  largeBounded := by norm_num [capacity, modulus]
  disjoint := Or.inl (by norm_num [capacity])

def globalEnv (layout : Layout) : Env :=
  bind (bind emptyEnv "rpc_small" (.ptr layout.smallBase))
    "rpc_large" (.ptr layout.largeBase)

theorem source_call_argument_evaluation (layout : Layout) (service : Service) :
    ([.nat input, .nat capacity, .var "rpc_small", .var "rpc_large"] : List Expr).mapM
      (evalPure service (initializedHeap layout) (globalEnv layout) 100) =
      some [.i64 input, .i32 capacity, .ptr layout.smallBase, .ptr layout.largeBase] := by
  simp [evalPure, literal, input, capacity, globalEnv, QuotientCMachine.bind, emptyEnv]
  <;> norm_num

theorem source_call_domain :
    2 ≤ input ∧ input ≤ 2000000000000 ∧ Nat.sqrt input < capacity ∧
      input < modulus ∧ capacity < modulus := by
  norm_num [input, capacity, modulus, Nat.sqrt_lt]

theorem source_argument_conversion :
    uint64 (.i64 input) = some (.u64 input) ∧
    uint64 (.i32 capacity) = some (.u64 capacity) := by
  norm_num [uint64, Value.scalar, input, capacity, modulus]

theorem source_pointer_values_valid (layout : Layout) :
    ValidValue (.ptr layout.smallBase) ∧ ValidValue (.ptr layout.largeBase) := by
  have hsmall := layout.smallBounded
  have hlarge := layout.largeBounded
  have hc : 0 < capacity := by norm_num [capacity]
  change layout.smallBase < modulus ∧ layout.largeBase < modulus
  omega

#print axioms source_static_initialization
#print axioms initialized_owned
#print axioms initialized_word_zero
#print axioms source_call_argument_evaluation
#print axioms source_call_domain
end RamanujanPV.QuotientDriverInit
