/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTTraceTwiddles

set_option autoImplicit false
noncomputable section
namespace RH080Next.FFT.IntegerModel

/-- A generic sparse mirrored input in the actual integer scale. -/
def sparseInput (d : Nat) (coefficient : Nat → Int) (n j : Nat) : CInt :=
  let k := if j<d then j else n-j
  if k<d then (coefficient k*100000000000000000000,0) else (0,0)

theorem sparseInput_zero (d n j : Nat) (coefficient : Nat → Int)
    (hl : d≤j) (hr : d≤n-j) : sparseInput d coefficient n j=(0,0) := by
  simp [sparseInput,not_lt.mpr hl,not_lt.mpr hr]

theorem sparse_zero_subtree (d n s index step : Nat) (coefficient : Nat → Int)
    (hn : n=step*2^s) (hleft : d ≤ index) (hright : index+d≤step) :
    ∀ j<2^s, sparseInput d coefficient n (index+step*j)=(0,0) := by
  intro j hj
  have hm := Nat.mul_le_mul_left step (Nat.succ_le_of_lt hj)
  simp only [Nat.mul_add,Nat.mul_one,Nat.succ_eq_add_one] at hm
  apply sparseInput_zero
  · omega
  · have hb : index+step*j+d≤n := by rw [hn]; omega
    omega

theorem sparse_zero_execution (stages : Nat → List CInt) (d n s index step : Nat)
    (coefficient : Nat → Int)
    (hlen : ∀ t<s,(stages (t+1)).length=2^t)
    (hn : n=step*2^s) (hleft : d ≤ index) (hright : index+d≤step) :
    ExecutionTrace stages (sparseInput d coefficient n) s index step
      (List.replicate (2^s) (0,0)) :=
  ExecutionTrace.zeros _ _ s index step hlen (sparse_zero_subtree d n s index step coefficient hn hleft hright)

/-- Segment endpoints permit independent checking and mathematical composition
of large global twiddle tables, with no hash equality used as a proof premise. -/
inductive TwiddleSegment (seed : CInt) : CInt → List CInt → CInt → Prop
  | nil (previous : CInt) : TwiddleSegment seed previous [] previous
  | cons (previous current final : CInt) (rest : List CInt)
      (hc : current=mul previous seed) (tail : TwiddleSegment seed current rest final) :
      TwiddleSegment seed previous (current::rest) final

def checkTwiddleSegment (seed : CInt) : CInt → List CInt → CInt → Bool
  | previous,[],final => decide (previous=final)
  | previous,current::rest,final => decide (current=mul previous seed) && checkTwiddleSegment seed current rest final

theorem checkTwiddleSegment_sound (seed previous final : CInt) (rest : List CInt)
    (h : checkTwiddleSegment seed previous rest final=true) : TwiddleSegment seed previous rest final := by
  induction rest generalizing previous with
  | nil =>
    simp only [checkTwiddleSegment,decide_eq_true_eq] at h
    subst final
    exact TwiddleSegment.nil _
  | cons current rest ih =>
    simp only [checkTwiddleSegment,Bool.and_eq_true,decide_eq_true_eq] at h
    exact TwiddleSegment.cons previous current final rest h.1 (ih current h.2)

theorem TwiddleSegment.append {seed previous middle final : CInt} {xs ys : List CInt}
    (h : TwiddleSegment seed previous xs middle) (hh : TwiddleSegment seed middle ys final) :
    TwiddleSegment seed previous (xs++ys) final := by
  induction h with
  | nil previous => exact hh
  | cons previous current final rest hc tail ih =>
    exact TwiddleSegment.cons _ _ _ _ hc (ih hh)

theorem TwiddleSegment.forget_final {seed previous final : CInt} {xs : List CInt}
    (h : TwiddleSegment seed previous xs final) : TwiddleTrace seed previous xs := by
  induction h with
  | nil previous => exact TwiddleTrace.nil _
  | cons previous current final rest hc tail ih => exact TwiddleTrace.cons _ _ _ hc ih

/-- Concatenating decimation chunks is valid only when the first input chunk
has even length. This excludes the singleton-boundary ambiguity. -/
theorem EvenTrace.append_even {as bs cs ds : List CInt}
    (h : EvenTrace as bs) (hh : EvenTrace cs ds) (heven : Even as.length) :
    EvenTrace (as++cs) (bs++ds) := by
  induction h with
  | nil => simpa using hh
  | one a => norm_num [Nat.not_even_one] at heven
  | cons a b as evens tail ih =>
    apply EvenTrace.cons a b _ _
    apply ih
    simpa [List.length_cons,Nat.even_add] using heven

theorem LayerTrace.append {ws : List CInt} {as bs outs as' bs' outs' : List (List CInt)}
    (h : LayerTrace ws as bs outs) (hh : LayerTrace ws as' bs' outs') :
    LayerTrace ws (as++as') (bs++bs') (outs++outs') := by
  induction h with
  | nil => simpa using hh
  | cons a b out as bs outs merge tail ih => exact LayerTrace.cons _ _ _ _ _ _ merge ih

/-- An even-length decimation block composes without an unchecked boundary. -/
structure EvenBlock (xs ys : List CInt) : Prop where
  trace : EvenTrace xs ys
  evenLength : Even xs.length

theorem EvenBlock.append {as bs cs ds : List CInt} (h : EvenBlock as bs) (hh : EvenBlock cs ds) :
    EvenBlock (as++cs) (bs++ds) :=
  ⟨h.trace.append_even hh.trace h.evenLength,by simpa using h.evenLength.add hh.evenLength⟩

/-- Chunk sums compose mathematically; no large terminal fold is trusted. -/
def absSum (xs : List CInt) : Nat := (xs.map (fun z => z.1.natAbs)).sum

theorem absSum_append (xs ys : List CInt) : absSum (xs++ys)=absSum xs+absSum ys := by
  simp [absSum]

theorem fold_absSum (xs : List CInt) (start : Nat) :
    xs.foldl (fun a z => a+z.1.natAbs) start=start+absSum xs := by
  induction xs generalizing start with
  | nil => simp [absSum]
  | cons z xs ih => simpa [absSum,Nat.add_assoc] using ih (start+z.1.natAbs)


#print axioms sparse_zero_execution
#print axioms checkTwiddleSegment_sound
#print axioms TwiddleSegment.append
#print axioms EvenTrace.append_even
#print axioms EvenBlock.append
#print axioms absSum_append
#print axioms fold_absSum
end RH080Next.FFT.IntegerModel
