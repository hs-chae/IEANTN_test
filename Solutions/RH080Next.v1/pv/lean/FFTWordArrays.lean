/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import GoldbachDirect.Memory
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

def integer64 (n : Nat) : Integer := ⟨.u64,n⟩
def wordPointer (object index : Nat) : Pointer := ⟨object,8*index,.u64⟩
def wordObject (length : Nat) (data : Nat → Nat) : Object :=
  {extent:=8*length,storage:=.host,cells:=fun offset =>
    if offset%8=0 ∧ offset/8<length then some (.integer (integer64 (data (offset/8)))) else none}

def WordArrayRep {F : Type} (state : State F) (object length : Nat) (data : Nat → Nat) : Prop :=
  state.mode=.host ∧ state.objects object=some (wordObject length data) ∧
    ∀i,i<length→data i<2^64

@[simp] theorem integer64_toInt (n : Nat) : (integer64 n).toInt=(n:Int) := by
  simp [integer64,Integer.toInt,IntKind.signed]

theorem cast64_exact (n : Nat) (hn : n<2^64) :
    Integer.cast .u64 (n:Int)=integer64 n := by
  change (⟨.u64,((n:Int)%((2^64:Nat):Int)).toNat⟩ : Integer)=⟨.u64,n⟩
  rw [←Int.natCast_emod,Nat.mod_eq_of_lt hn]
  rfl

@[simp] theorem convert64 (n : Nat) (hn : n<2^64) :
    Value.convert .u64 (.integer (integer64 n))=some (.integer (integer64 n)) := by
  simp [Value.convert,CType.integer,cast64_exact n hn]

theorem word_load {F : Type} {state : State F} {object length index : Nat}
    {data : Nat → Nat} (rep : WordArrayRep state object length data) (hi : index<length) :
    state.load (wordPointer object index)=some (.integer (integer64 (data index))) := by
  rcases rep with ⟨mode,present,fit⟩
  have hbytes : 8*index+8≤8*length := by omega
  simp [State.load,wordPointer,present,CType.byteSize,State.accessible,wordObject,
    mode,hi,hbytes,integer64,IntKind.width]
  exact convert64 (data index) (fit index hi)

theorem word_offsets_disjoint (i j : Nat) (hne : i≠j) :
    ¬(8*i<8*j+8 ∧8*j<8*i+8) := by omega

/-- Base-10^9 schoolbook digit multiplication never overflows a C uint64_t.
The invariant allows one previous digit and one carry in each actual source t. -/
theorem schoolbook_digit_safe (a b digit carry : Nat)
    (ha : a<1000000000) (hb : b<1000000000)
    (hd : digit<1000000000) (hc : carry<1000000000) :
    digit+a*b+carry<2^64 := by
  have hp : a*b≤999999998000000001 := by
    exact (Nat.mul_le_mul (by omega : a≤999999999) (by omega : b≤999999999))
  omega

/-- Every signed floor in fixed_multiply has less than one unit error. This
lemma is about the actual floor convention, including negative products. -/
theorem signed_floor_error (a : Int) (u : Nat) (hu : 0<u) :
    (a : ℚ)/(u:ℚ)-1 < (a/(u:Int) : Int) ∧
    ((a/(u:Int) : Int) : ℚ)≤(a:ℚ)/(u:ℚ) := by
  have hmod := Int.emod_nonneg a (by omega : (u:Int)≠0)
  have hlt := Int.emod_lt_of_pos a (by omega : 0<(u:Int))
  have hid := Int.emod_add_mul_ediv a (u:Int)
  have hreal : (a:ℚ)=(a%(u:Int):Int)+(u:ℚ)*(a/(u:Int):Int) := by exact_mod_cast hid.symm
  have hmodq : (0:ℚ)≤(a%(u:Int):Int) := by exact_mod_cast hmod
  have hltq : ((a%(u:Int):Int):ℚ)<(u:ℚ) := by exact_mod_cast hlt
  have huq : (0:ℚ)<(u:ℚ) := by exact_mod_cast hu
  have hlo : (a:ℚ)/(u:ℚ) < (a/(u:Int):Int)+1 :=
    (div_lt_iff₀ huq).mpr (by nlinarith [hreal,hltq])
  have hhi : ((a/(u:Int):Int):ℚ) ≤ (a:ℚ)/(u:ℚ) :=
    (le_div_iff₀ huq).mpr (by nlinarith [hreal,hmodq])
  exact ⟨by linarith,hhi⟩

#print axioms word_load
#print axioms schoolbook_digit_safe
end RH080Next.FFTPV.WordArrays
