/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductOuterLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductOuter
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open ApplicationBirthFrame

theorem shift_update (data : Nat→Nat) (start index digit : Nat) :
    (fun k=>Function.update data (start+index) digit (start+k))=
      Function.update (fun k=>data (start+k)) index digit := by
  funext k
  by_cases same : k=index
  · subst k;simp
  · have different : start+k≠start+index:=by omega
    simp [Function.update_of_ne same,Function.update_of_ne different]

/-- The exact row recurrence respects subrange addressing. This mathematical
lemma is linked below to the actual typed-memory source row execution. -/
theorem row_shift (B start offset a : Nat) (b data : Nat→Nat) (n : Nat) :
    ((fun k=>(RH080Next.FFT.Limbs.row B (start+offset) a b data n).1 (start+k)),
      (RH080Next.FFT.Limbs.row B (start+offset) a b data n).2)=
      RH080Next.FFT.Limbs.row B offset a b (fun k=>data (start+k)) n := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    let r:=RH080Next.FFT.Limbs.row B (start+offset) a b data n
    let s:=RH080Next.FFT.Limbs.row B offset a b (fun k=>data (start+k)) n
    have sameData : (fun k=>r.1 (start+k))=s.1:=congrArg Prod.fst ih
    have sameCarry:=congrArg (fun p : (Nat→Nat)×Nat=>p.2) ih
    change r.2=s.2 at sameCarry
    have sameTotal : r.1 (start+offset+n)+a*b n+r.2=s.1 (offset+n)+a*b n+s.2:=by
      rw [show start+offset+n=start+(offset+n) by omega,congrFun sameData (offset+n),sameCarry]
    change ((fun k=>Function.update r.1 (start+offset+n)
        ((r.1 (start+offset+n)+a*b n+r.2)%B) (start+k)),
        (r.1 (start+offset+n)+a*b n+r.2)/B)=
      (Function.update s.1 (offset+n) ((s.1 (offset+n)+a*b n+s.2)%B),
        (s.1 (offset+n)+a*b n+s.2)/B)
    rw [sameTotal,show start+offset+n=start+(offset+n) by omega,shift_update,sameData]

/-- Reads/writes inside ten product digits do not depend on unrelated words
outside that scratch subrange. The terminal carry is proved equal too. -/
theorem row_congr_ten (B offset a : Nat) (b left right : Nat→Nat) (n : Nat)
    (bound : offset+n≤10) (same : ∀k,k<10 → left k=right k) :
    (RH080Next.FFT.Limbs.row B offset a b left n).2=(RH080Next.FFT.Limbs.row B offset a b right n).2 ∧
      ∀k,k<10 → (RH080Next.FFT.Limbs.row B offset a b left n).1 k=(RH080Next.FFT.Limbs.row B offset a b right n).1 k := by
  induction n with
  | zero=>exact ⟨rfl,same⟩
  | succ n ih=>
    obtain ⟨sameCarry,sameData⟩:=ih (by omega)
    let r:=RH080Next.FFT.Limbs.row B offset a b left n
    let s:=RH080Next.FFT.Limbs.row B offset a b right n
    have sameTotal : r.1 (offset+n)+a*b n+r.2=s.1 (offset+n)+a*b n+s.2:=by
      rw [sameData (offset+n) (by omega),sameCarry]
    constructor
    · change (r.1 (offset+n)+a*b n+r.2)/B=(s.1 (offset+n)+a*b n+s.2)/B
      rw [sameTotal]
    · intro k hk
      change Function.update r.1 (offset+n) ((r.1 (offset+n)+a*b n+r.2)%B) k=
        Function.update s.1 (offset+n) ((s.1 (offset+n)+a*b n+s.2)%B) k
      rw [sameTotal]
      by_cases exactIndex : k=offset+n
      · subst k;simp
      · simpa [Function.update_of_ne exactIndex] using sameData k hk

theorem rowResult_matches (start i : Nat) (a b data : Nat→Nat)
    (hi : i<5) (input : ∀k,k<10 → data (start+k)=RH080Next.FFT.Limbs.rows 1000000000 5 a b i k) :
    ∀k,k<10 → rowResult start i a b data (start+k)=RH080Next.FFT.Limbs.rows 1000000000 5 a b (i+1) k := by
  have shift:=row_shift 1000000000 start i (a i) b data 5
  have shiftData:=congrArg Prod.fst shift
  have shiftCarry:=congrArg Prod.snd shift
  change (fun k=>(RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).1 (start+k))=
    (RH080Next.FFT.Limbs.row 1000000000 i (a i) b (fun k=>data (start+k)) 5).1 at shiftData
  change (RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).2=
    (RH080Next.FFT.Limbs.row 1000000000 i (a i) b (fun k=>data (start+k)) 5).2 at shiftCarry
  have congr:=row_congr_ten 1000000000 i (a i) b (fun k=>data (start+k))
    (RH080Next.FFT.Limbs.rows 1000000000 5 a b i) 5 (by omega) input
  intro k hk
  simp only [rowResult,RH080Next.FFT.Limbs.rows]
  rw [congrFun (shift_update (RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).1 start (i+5)
    (RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).2) k]
  change Function.update (fun k=>(RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).1 (start+k)) (i+5)
    (RH080Next.FFT.Limbs.row 1000000000 (start+i) (a i) b data 5).2 k=_
  rw [shiftData,shiftCarry,congr.1]
  by_cases same : k=i+5
  · subst k;simp
  · simpa [Function.update_of_ne same] using congr.2 k hk

/-- Every source row extends the exact full multiplication prefix. Only the
ten initialized scratch words are required to be zero at entry. -/
theorem advance_matches (start i steps : Nat) (a b data : Nat→Nat)
    (range : i+steps≤5) (input : ∀k,k<10 → data (start+k)=RH080Next.FFT.Limbs.rows 1000000000 5 a b i k) :
    ∀k,k<10 → advance start a b i data steps (start+k)=RH080Next.FFT.Limbs.rows 1000000000 5 a b (i+steps) k := by
  induction steps generalizing i data with
  | zero=>simpa [advance] using input
  | succ steps ih=>
    have row:=rowResult_matches start i a b data (by omega) input
    simpa only [advance,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      ih (i:=i+1) (data:=rowResult start i a b data) (by omega) row

/-- The actual complete twenty-five source digit iterations compute the full
base-billion product. Scratch and the input arrays are actual typed memory;
the zero initialization is an explicit entry obligation, not a trusted effect. -/
theorem source_product_core {F : Type} (context : Context F) {before : State F}
    {aObj aSize aStart bObj bSize bStart workObj workSize workStart : Nat}
    {ids owners : PVar→Nat} {a b data : Nat→Nat}
    (h : View before aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b data 0)
    (initialized : ∀k,k<10 → data (workStart+k)=0) :
    ∃after finalData,Exec context before outerLoop .normal after ∧
      View after aObj aSize aStart bObj bSize bStart workObj workSize workStart ids owners a b finalData 5 ∧
      Frame before.nextObject before after [workObj,ids PVar.i] ∧
      RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>finalData (workStart+k))=
        RH080Next.FFT.Limbs.value 1000000000 5 a*RH080Next.FFT.Limbs.value 1000000000 5 b := by
  obtain ⟨after,run,ha,frame⟩:=loop_execution context 5 h (by rfl)
  have input : ∀k,k<10 → data (workStart+k)=RH080Next.FFT.Limbs.rows 1000000000 5 a b 0 k:=initialized
  have final:=advance_matches workStart 0 5 a b data (by norm_num) input
  refine ⟨after,advance workStart a b 0 data 5,run,ha,frame,?_⟩
  have sameValue : RH080Next.FFT.Limbs.value 1000000000 10 (fun k=>advance workStart a b 0 data 5 (workStart+k))=
      RH080Next.FFT.Limbs.value 1000000000 10 (RH080Next.FFT.Limbs.rows 1000000000 5 a b 5) := by
    unfold RH080Next.FFT.Limbs.value
    apply Finset.sum_congr rfl
    intro k hk
    simp only [final k (Finset.mem_range.mp hk)]
  exact sameValue.trans (RH080Next.FFT.Limbs.five_by_five_product a b)

#print axioms row_shift
#print axioms row_congr_ten
#print axioms rowResult_matches
#print axioms advance_matches
#print axioms source_product_core
end RH080Next.FFTPV.ProductOuter
