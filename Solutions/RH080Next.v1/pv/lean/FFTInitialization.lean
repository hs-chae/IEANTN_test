/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTWordStore
import GoldbachDirect.PlatformMemory
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.WordArrays
open GoldbachDirect

/-- Actual calloc bytes become typed words only through the application's own
stores. The filled contains u64 zero cells; the remainder is still zero bytes. -/
def zeroPrefixObject (length filled : Nat) : Object :=
  {extent:=8*length,storage:=.host,cells:=fun offset =>
    if offset%8=0 ∧offset/8<filled then some (.integer (integer64 0))
    else if offset<8*length ∧8*filled≤offset then some (.integer ⟨.u8,0⟩) else none}

theorem zeroPrefix_zero (length : Nat) : zeroPrefixObject length 0 =
    ({extent:=8*length,storage:=.host,cells:=PlatformMemory.zeroBytes (8*length)} : Object) := by
  unfold zeroPrefixObject
  congr 1
  funext offset
  simp [PlatformMemory.zeroBytes]

theorem zeroPrefix_full (length : Nat) : zeroPrefixObject length length =
    wordObject length (fun _=>0) := by
  unfold zeroPrefixObject wordObject
  congr 1
  funext offset
  by_cases h : offset%8=0 ∧offset/8<length
  · simp [h]
  · have hn : ¬(offset<8*length ∧8*length≤offset) := by omega
    simp [h,hn]

theorem zeroPrefix_store {F : Type} {state : State F} {object length filled : Nat}
    (mode : state.mode=.host) (present : state.objects object=some (zeroPrefixObject length filled))
    (hp : filled<length) :
    state.store (wordPointer object filled) (.integer (integer64 0)) =
      some {state with objects := fun key => if key=object then some (zeroPrefixObject length (filled+1)) else state.objects key} := by
  have hbytes : 8*filled+8≤8*length := by omega
  simp [State.store,wordPointer,present,CType.byteSize,State.accessible,zeroPrefixObject,
    mode,hbytes,convert64 0 (by norm_num)]
  funext key
  split_ifs with same
  · congr 1
    congr 1
    funext offset
    by_cases heq : offset=8*filled
    · subst offset
      simp [hp]
    · have hd := Nat.mod_add_div offset 8
      by_cases hw : offset%8=0 ∧offset/8<filled
      · have hwn : offset%8=0 ∧offset/8<filled+1 := by omega
        have hsafe : offset+8≤8*filled := by omega
        have hindex : offset/8≤filled := by omega
        simp [heq,hw,hindex,Option.filter,integer64,hsafe]
      · by_cases hwn : offset%8=0 ∧offset/8<filled+1
        · exfalso
          omega
        · have hwn' : ¬(offset%8=0 ∧offset/8≤filled) := by omega
          by_cases hb : offset<8*length ∧8*filled≤offset
          · by_cases near : offset<8*filled+8
            · have hbn : ¬(offset<8*length ∧8*(filled+1)≤offset) := by omega
              simp [heq,hw,hwn',hb,hbn,Option.filter,near]
              omega
            · have hbn : offset<8*length ∧8*(filled+1)≤offset := by omega
              simp [heq,hw,hwn',hb,hbn,Option.filter,near]
          · have hbn : ¬(offset<8*length ∧8*(filled+1)≤offset) := by omega
            simp [heq,hw,hwn',hb,hbn,Option.filter]
  · rfl

#print axioms zeroPrefix_zero
#print axioms zeroPrefix_full
#print axioms zeroPrefix_store
end RH080Next.FFTPV.WordArrays
