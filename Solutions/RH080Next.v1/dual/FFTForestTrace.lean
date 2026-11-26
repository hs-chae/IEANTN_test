/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTraceChecker

set_option autoImplicit false
namespace RH080Next.FFT.IntegerModel

/-- Independent relation for one complete layer of the actual recursive FFT.
Each pair of child vectors is merged using the same globally-strided table. -/
inductive LayerTrace (ws : List CInt) : List (List CInt) → List (List CInt) → List (List CInt) → Prop
  | nil : LayerTrace ws [] [] []
  | cons (as bs out : List CInt) (ass bss outs : List (List CInt))
      (merge : MergeTrace as bs ws (out.take as.length) (out.drop as.length))
      (tail : LayerTrace ws ass bss outs) :
      LayerTrace ws (as::ass) (bs::bss) (out::outs)

def checkLayer (ws : List CInt) : List (List CInt) → List (List CInt) → List (List CInt) → Bool
  | [],[],[] => true
  | as::ass,bs::bss,out::outs =>
    checkMerge as bs ws (out.take as.length) (out.drop as.length) && checkLayer ws ass bss outs
  | _,_,_ => false

theorem checkLayer_sound (ws : List CInt) (ass bss outs : List (List CInt))
    (h : checkLayer ws ass bss outs=true) : LayerTrace ws ass bss outs := by
  induction ass generalizing bss outs with
  | nil =>
    cases bss <;> cases outs <;> simp_all [checkLayer]
    exact LayerTrace.nil
  | cons as ass ih =>
    cases bss with
    | nil => simp [checkLayer] at h
    | cons bs bss =>
      cases outs with
      | nil => simp [checkLayer] at h
      | cons out outs =>
        simp only [checkLayer,Bool.and_eq_true] at h
        exact LayerTrace.cons as bs out ass bss outs
          (checkMerge_sound _ _ _ _ _ h.1) (ih _ _ h.2)

theorem LayerTrace.lengths {ws : List CInt} {ass bss outs : List (List CInt)}
    (h : LayerTrace ws ass bss outs) : ass.length=bss.length ∧ ass.length=outs.length := by
  induction h with
  | nil => simp
  | cons as bs out ass bss outs merge tail ih => simpa using ih

/-- Consecutively indexed independent executions. The relation is specified
by the execution semantics, not by any certificate acceptance function. -/
inductive ForestTrace (stages : Nat → List CInt) (input : Nat → CInt) (s step : Nat) :
    Nat → List (List CInt) → Prop
  | nil (index : Nat) : ForestTrace stages input s step index []
  | cons (index : Nat) (out : List CInt) (outs : List (List CInt))
      (head : ExecutionTrace stages input s index step out)
      (tail : ForestTrace stages input s step (index+1) outs) :
      ForestTrace stages input s step index (out::outs)

theorem ForestTrace.take {stages : Nat → List CInt} {input : Nat → CInt}
    {s step index : Nat} {outs : List (List CInt)}
    (h : ForestTrace stages input s step index outs) (n : Nat) :
    ForestTrace stages input s step index (outs.take n) := by
  induction h generalizing n with
  | nil index => simpa using (ForestTrace.nil (stages := stages) (input := input) (s := s) (step := step) index)
  | cons index out outs head tail ih =>
    cases n with
    | zero => exact ForestTrace.nil _
    | succ n => exact ForestTrace.cons _ _ _ head (ih n)

theorem ForestTrace.drop {stages : Nat → List CInt} {input : Nat → CInt}
    {s step index : Nat} {outs : List (List CInt)}
    (h : ForestTrace stages input s step index outs) (n : Nat) (hn : n≤outs.length) :
    ForestTrace stages input s step (index+n) (outs.drop n) := by
  induction h generalizing n with
  | nil index =>
    have hn0 : n=0 := by simpa using hn
    subst n
    exact ForestTrace.nil _
  | cons index out outs head tail ih =>
    cases n with
    | zero => simpa using ForestTrace.cons _ _ _ head tail
    | succ n =>
      have hn' : n≤outs.length := by simpa using hn
      simpa only [List.drop_succ_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih n hn'

theorem LayerTrace.executions {stages : Nat → List CInt} {input : Nat → CInt}
    {s step index : Nat} {ass bss outs : List (List CInt)}
    (h : LayerTrace (stages (s+1)) ass bss outs)
    (left : ForestTrace stages input s (step*2) index ass)
    (right : ForestTrace stages input s (step*2) (index+step) bss) :
    ForestTrace stages input (s+1) step index outs := by
  induction h generalizing index with
  | nil => exact ForestTrace.nil _
  | cons as bs out ass bss outs merge tail ih =>
    cases left with
    | cons _ _ _ hl hls =>
      cases right with
      | cons _ _ _ hr hrs =>
        have hm := ExecutionTrace.node s index step _ _ _ _ hl hr merge
        rw [List.take_append_drop] at hm
        apply ForestTrace.cons _ _ _ hm
        apply ih hls
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrs

theorem layer_step {stages : Nat → List CInt} {input : Nat → CInt}
    {s step : Nat} {previous out : List (List CInt)}
    (hprev : ForestTrace stages input s (step*2) 0 previous)
    (hlen : previous.length=step*2)
    (h : LayerTrace (stages (s+1)) (previous.take step) (previous.drop step) out) :
    ForestTrace stages input (s+1) step 0 out := by
  exact h.executions (hprev.take step) (by simpa using hprev.drop step (by omega))

theorem leaf_forest (stages : Nat → List CInt) (input : Nat → CInt) (n step : Nat) :
    ForestTrace stages input 0 step 0 ((List.range n).map (fun j => [input j])) := by
  have aux : ∀ (n index : Nat), ForestTrace stages input 0 step index
      ((List.range' index n).map (fun j => [input j])) := by
    intro n
    induction n with
    | zero => intro index; exact ForestTrace.nil _
    | succ n ih =>
      intro index
      simpa only [List.range'_succ,List.map_cons] using
        ForestTrace.cons index [input index] _ (ExecutionTrace.leaf index step) (ih (index+1))
  simpa only [List.range_eq_range'] using aux n 0

theorem singleton_execution {stages : Nat → List CInt} {input : Nat → CInt}
    {s step index : Nat} {out : List CInt}
    (h : ForestTrace stages input s step index [out]) : ExecutionTrace stages input s index step out := by
  cases h with
  | cons _ _ _ head _ => exact head

#print axioms checkLayer_sound
#print axioms LayerTrace.executions
#print axioms layer_step
#print axioms leaf_forest
end RH080Next.FFT.IntegerModel
