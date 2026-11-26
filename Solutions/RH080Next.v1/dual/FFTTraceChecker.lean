/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTPairedIntModel

set_option autoImplicit false
namespace RH080Next.FFT.IntegerModel

/-- Independent operational relation for a sequence of actual fixed-point
butterflies. It does not refer to the Boolean certificate checker. -/
inductive MergeTrace : List CInt → List CInt → List CInt → List CInt → List CInt → Prop
  | nil : MergeTrace [] [] [] [] []
  | cons (a b w p q : CInt) (as bs ws ps qs : List CInt)
      (hp : p=add a (mul b w)) (hq : q=sub a (mul b w))
      (tail : MergeTrace as bs ws ps qs) :
      MergeTrace (a::as) (b::bs) (w::ws) (p::ps) (q::qs)

def checkMerge : List CInt → List CInt → List CInt → List CInt → List CInt → Bool
  | [],[],[],[],[] => true
  | a::as,b::bs,w::ws,p::ps,q::qs =>
    decide (p=add a (mul b w)) && decide (q=sub a (mul b w)) && checkMerge as bs ws ps qs
  | _,_,_,_,_ => false

theorem checkMerge_sound (as bs ws ps qs : List CInt)
    (h : checkMerge as bs ws ps qs=true) : MergeTrace as bs ws ps qs := by
  induction as generalizing bs ws ps qs with
  | nil =>
    cases bs <;> cases ws <;> cases ps <;> cases qs <;> simp_all [checkMerge]
    exact MergeTrace.nil
  | cons a as ih =>
    cases bs with
    | nil => simp [checkMerge] at h
    | cons b bs =>
      cases ws with
      | nil => simp [checkMerge] at h
      | cons w ws =>
        cases ps with
        | nil => simp [checkMerge] at h
        | cons p ps =>
          cases qs with
          | nil => simp [checkMerge] at h
          | cons q qs =>
            simp only [checkMerge,Bool.and_eq_true,decide_eq_true_eq] at h
            exact MergeTrace.cons a b w p q as bs ws ps qs h.1.1 h.1.2 (ih _ _ _ _ h.2)

/-- Independent operational relation for the global twiddle recurrence. -/
inductive TwiddleTrace (seed : CInt) : CInt → List CInt → Prop
  | nil (previous : CInt) : TwiddleTrace seed previous []
  | cons (previous current : CInt) (rest : List CInt)
      (hc : current=mul previous seed) (tail : TwiddleTrace seed current rest) :
      TwiddleTrace seed previous (current::rest)

def checkTwiddles (seed : CInt) : CInt → List CInt → Bool
  | _,[] => true
  | previous,current::rest => decide (current=mul previous seed) && checkTwiddles seed current rest

theorem checkTwiddles_sound (seed previous : CInt) (rest : List CInt)
    (h : checkTwiddles seed previous rest=true) : TwiddleTrace seed previous rest := by
  induction rest generalizing previous with
  | nil => exact TwiddleTrace.nil previous
  | cons current rest ih =>
    simp only [checkTwiddles,Bool.and_eq_true,decide_eq_true_eq] at h
    exact TwiddleTrace.cons previous current rest h.1 (ih current h.2)

theorem MergeTrace.lengths {as bs ws ps qs : List CInt} (h : MergeTrace as bs ws ps qs) :
    as.length=bs.length ∧ as.length=ws.length ∧ as.length=ps.length ∧ as.length=qs.length := by
  induction h with
  | nil => simp
  | cons a b w p q as bs ws ps qs hp hq tail ih => simpa using ih

theorem MergeTrace.deterministic {as bs ws ps qs ps' qs' : List CInt}
    (h : MergeTrace as bs ws ps qs) (h' : MergeTrace as bs ws ps' qs') : ps=ps' ∧ qs=qs' := by
  induction h generalizing ps' qs' with
  | nil => cases h'; exact ⟨rfl,rfl⟩
  | cons a b w p q as bs ws ps qs hp hq tail ih =>
    cases h' with
    | cons _ _ _ p' q' _ _ _ ps' qs' hp' hq' tail' =>
      have ht := ih tail'
      exact ⟨by rw [hp,hp',ht.1],by rw [hq,hq',ht.2]⟩

theorem MergeTrace.append {as bs ws ps qs as' bs' ws' ps' qs' : List CInt}
    (h : MergeTrace as bs ws ps qs) (h' : MergeTrace as' bs' ws' ps' qs') :
    MergeTrace (as++as') (bs++bs') (ws++ws') (ps++ps') (qs++qs') := by
  induction h with
  | nil => simpa using h'
  | cons a b w p q as bs ws ps qs hp hq tail ih =>
    exact MergeTrace.cons _ _ _ _ _ _ _ _ _ _ hp hq ih

theorem MergeTrace.zeros (ws : List CInt) :
    MergeTrace (List.replicate ws.length (0,0)) (List.replicate ws.length (0,0)) ws
      (List.replicate ws.length (0,0)) (List.replicate ws.length (0,0)) := by
  induction ws with
  | nil => exact MergeTrace.nil
  | cons w ws ih =>
    apply MergeTrace.cons _ _ _ _ _ _ _ _ _ _ _ _ ih
    · simp [add,mul,unit]
    · simp [sub,mul,unit]

/-- Relational specification of the recursive integer FFT. Its constructors
do not invoke a Boolean checker or assume a desired numerical enclosure. -/
inductive ExecutionTrace (stages : Nat → List CInt) (input : Nat → CInt) :
    Nat → Nat → Nat → List CInt → Prop
  | leaf (index step : Nat) : ExecutionTrace stages input 0 index step [input index]
  | node (s index step : Nat) (as bs ps qs : List CInt)
      (left : ExecutionTrace stages input s index (step*2) as)
      (right : ExecutionTrace stages input s (index+step) (step*2) bs)
      (merge : MergeTrace as bs (stages (s+1)) ps qs) :
      ExecutionTrace stages input (s+1) index step (ps++qs)

theorem ExecutionTrace.output_length {stages : Nat → List CInt} {input : Nat → CInt}
    {s index step : Nat} {out : List CInt} (h : ExecutionTrace stages input s index step out) :
    out.length=2^s := by
  induction h with
  | leaf index step => rfl
  | node s index step as bs ps qs left right merge ihl ihr =>
    have hm := merge.lengths
    rw [List.length_append,←hm.2.2.1,←hm.2.2.2,ihl,Nat.pow_succ]
    omega

theorem ExecutionTrace.deterministic {stages : Nat → List CInt} {input : Nat → CInt}
    {s index step : Nat} {out out' : List CInt}
    (h : ExecutionTrace stages input s index step out)
    (h' : ExecutionTrace stages input s index step out') : out=out' := by
  induction h generalizing out' with
  | leaf index step => cases h'; rfl
  | node s index step as bs ps qs left right merge ihl ihr =>
    cases h' with
    | node _ _ _ as' bs' ps' qs' left' right' merge' =>
      have ha := ihl left'
      have hb := ihr right'
      subst as'
      subst bs'
      obtain ⟨hp,hq⟩ := merge.deterministic merge'
      rw [hp,hq]

theorem ExecutionTrace.zeros (stages : Nat → List CInt) (input : Nat → CInt)
    (s index step : Nat)
    (hstage : ∀ t < s, (stages (t+1)).length=2^t)
    (hz : ∀ j < 2^s, input (index+step*j)=(0,0)) :
    ExecutionTrace stages input s index step (List.replicate (2^s) (0,0)) := by
  induction s generalizing index step with
  | zero =>
    have h := hz 0 (by decide)
    simp only [Nat.mul_zero,Nat.add_zero] at h
    simpa only [Nat.pow_zero,List.replicate_one,h] using ExecutionTrace.leaf (stages := stages) (input := input) index step
  | succ s ih =>
    have hst : ∀ t < s, (stages (t+1)).length=2^t := fun t ht => hstage t (by omega)
    have hl : ∀ j < 2^s, input (index+(step*2)*j)=(0,0) := by
      intro j hj
      have h := hz (2*j) (by rw [Nat.pow_succ]; omega)
      simpa only [Nat.mul_assoc,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have hr : ∀ j < 2^s, input ((index+step)+(step*2)*j)=(0,0) := by
      intro j hj
      have h := hz (2*j+1) (by rw [Nat.pow_succ]; omega)
      simpa only [Nat.mul_assoc,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    have left := ih index (step*2) hst hl
    have right := ih (index+step) (step*2) hst hr
    have hm := MergeTrace.zeros (stages (s+1))
    rw [hstage s (by omega)] at hm
    have h := ExecutionTrace.node s index step _ _ _ _ left right hm
    convert h using 1
    rw [←List.replicate_add]
    congr 1
    rw [Nat.pow_succ]
    omega

/-- Checkable decimation of the global twiddle table. The actual C source
reads strided global entries, rather than recomputing smaller roots. -/
inductive EvenTrace : List CInt → List CInt → Prop
  | nil : EvenTrace [] []
  | one (a : CInt) : EvenTrace [a] [a]
  | cons (a b : CInt) (as evens : List CInt) (tail : EvenTrace as evens) :
      EvenTrace (a::b::as) (a::evens)

def checkEvens : List CInt → List CInt → Bool
  | [],[] => true
  | [a],[b] => decide (a=b)
  | a::_::as,b::bs => decide (a=b) && checkEvens as bs
  | _,_ => false

theorem checkEvens_sound (as bs : List CInt) (h : checkEvens as bs=true) : EvenTrace as bs := by
  induction as using List.twoStepInduction generalizing bs with
  | nil => cases bs <;> simp_all [checkEvens]; exact EvenTrace.nil
  | singleton a =>
    cases bs with
    | nil => simp [checkEvens] at h
    | cons b bs =>
      cases bs with
      | nil => simp only [checkEvens,decide_eq_true_eq] at h; subst b; exact EvenTrace.one a
      | cons c cs => simp [checkEvens] at h
  | cons_cons a b as ih =>
    cases bs with
    | nil => simp [checkEvens] at h
    | cons c cs =>
      simp only [checkEvens,Bool.and_eq_true,decide_eq_true_eq] at h
      rcases h with ⟨rfl,hh⟩
      exact EvenTrace.cons a b as cs (ih _ hh)

#print axioms checkMerge_sound
#print axioms checkTwiddles_sound
#print axioms MergeTrace.deterministic
#print axioms ExecutionTrace.deterministic
#print axioms ExecutionTrace.zeros
#print axioms checkEvens_sound
end RH080Next.FFT.IntegerModel
