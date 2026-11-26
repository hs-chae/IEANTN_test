/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordArrays
import Mathlib.Data.List.TakeDrop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.EncodedSelector
open GoldbachDirect

/-- The finite decision tree used by the actual source's locked-input lookup.
This is an input table, not a hardcoded numerical integration result. -/
inductive Tree where
  | leaf (value : Nat)
  | branch (cut : Nat) (left right : Tree)
  deriving DecidableEq

def Tree.value : Tree→Nat→Nat
  | .leaf v,_=>v
  | .branch cut left right,j=>if j<cut then left.value j else right.value j

def Tree.statement : Tree→Stmt
  | .leaf v=>.returnValue (some (.literal (.integer v "ULL")))
  | .branch cut left right=>.ite (.binary .lt (.variable "j") (.literal (.integer cut "ULL")))
      (.block [left.statement]) (some (.block [right.statement]))

def build : Nat→Nat→List Nat→Tree
  | 0,_,values=>.leaf (values.headD 0)
  | fuel+1,base,values=>
    if values.length≤1 then .leaf (values.headD 0)
    else let split:=values.length/2
      .branch (base+split) (build fuel base (values.take split))
        (build fuel (base+split) (values.drop split))

/-- Independent table-coverage relation. Its constructors specify literal
leaves and contiguous disjoint branch intervals; it does not mention a checker. -/
inductive Covers : Tree→Nat→List Nat→Prop where
  | leaf (v base : Nat) : Covers (.leaf v) base [v]
  | branch (base : Nat) (left right : Tree) (ls rs : List Nat)
      (leftCovers : Covers left base ls) (rightCovers : Covers right (base+ls.length) rs) :
      Covers (.branch (base+ls.length) left right) base (ls++rs)

theorem build_covers (fuel base : Nat) (values : List Nat)
    (nonempty : values≠[]) (enough : values.length≤fuel+1) : Covers (build fuel base values) base values:=by
  induction fuel generalizing base values with
  | zero=>
    cases values with
    | nil=>contradiction
    | cons x xs=>
      cases xs with
      | nil=>exact Covers.leaf x base
      | cons y ys=>simp at enough
  | succ fuel ih=>
    by_cases short : values.length≤1
    · cases values with
      | nil=>contradiction
      | cons x xs=>
        cases xs with
        | nil=>simpa only [build,List.length_singleton,le_refl,↓reduceIte,List.headD_cons] using Covers.leaf x base
        | cons y ys=>simp at short
    · let split:=values.length/2
      have positive : 0<split:=by dsimp [split];omega
      have smaller : split<values.length:=by dsimp [split];omega
      have leftLength : (values.take split).length=split:=by simp [List.length_take,Nat.min_eq_left (by omega : split≤values.length)]
      have rightLength : (values.drop split).length=values.length-split:=by simp
      have leftNonempty : values.take split≠[]:=by intro no;rw [no] at leftLength;simp at leftLength;omega
      have rightNonempty : values.drop split≠[]:=by intro no;rw [no] at rightLength;simp at rightLength;omega
      have leftBound : (values.take split).length≤fuel+1:=by rw [leftLength];dsimp [split];omega
      have rightBound : (values.drop split).length≤fuel+1:=by rw [rightLength];dsimp [split];omega
      have hl:=ih base (values.take split) leftNonempty leftBound
      have hr:=ih (base+split) (values.drop split) rightNonempty rightBound
      have result:=Covers.branch base _ _ _ _ hl (by simpa only [leftLength] using hr)
      simpa only [build,short,↓reduceIte,leftLength,List.take_append_drop] using result

theorem Covers.value_eq {tree : Tree} {base : Nat} {values : List Nat}
    (h : Covers tree base values) (i : Nat) (bound : i<values.length) :
    tree.value (base+i)=(values[i]?).getD 0:=by
  induction h generalizing i with
  | leaf v base=>
    have zero : i=0:=by simpa using bound
    subst i
    simp [Tree.value]
  | branch base left right ls rs hl hr ihl ihr=>
    by_cases low : i<ls.length
    · have hlv:=ihl i low
      simp only [Tree.value,show base+i<base+ls.length from by omega,↓reduceIte]
      simpa [List.getElem?_append,low] using hlv
    · have rightBound : i-ls.length<rs.length:=by simp only [List.length_append] at bound;omega
      have hrv:=ihr (i-ls.length) rightBound
      simp only [Tree.value,show ¬base+i<base+ls.length from by omega,↓reduceIte]
      rw [show base+i=(base+ls.length)+(i-ls.length) from by omega]
      simpa [List.getElem?_append,low] using hrv

#print axioms build_covers
#print axioms Covers.value_eq
end RH080Next.FFTPV.EncodedSelector
