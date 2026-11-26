/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroFrame
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem u64_storable (n : Nat) (hn : n<2^64) :
    Storable .u64 (.integer (integer64 n)) := by
  have hb : (Value.integer (integer64 n)).byteSize=8 := stored_u64_width n
  exact ⟨by rw [hb]; rfl,by rw [hb]; decide,convert64 n hn⟩

theorem pointer_storable (object : Nat) :
    Storable (.pointer .u64) (.pointer (wordPointer object 0)) := by
  have hb : (Value.pointer (wordPointer object 0)).byteSize=8 := stored_pointer_width _
  exact ⟨by rw [hb]; rfl,by rw [hb]; decide,by rfl⟩

/-- Actual declaration success follows from fresh language allocation and the
proved C type conversion, not an application initialization assumption. -/
theorem declare_exists {F : Type} {before : State F} (well : WellScoped before)
    (ctype : CType) (cname : String) (v : Value) (hv : Storable ctype v) :
    ∃after,before.declare ctype cname (some v)=some after := by
  have fresh : before.objects before.nextObject=none := by
    cases h : before.objects before.nextObject with
    | none => rfl
    | some old => have impossible:=well.objectIds _ old h; omega
  simp [State.declare,State.allocate,fresh,State.store,State.accessible,hv.typeWidth,hv.converted]

private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue)
    (d : Declaration before after cname newtype newvalue)
    (different : id≠before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable,by rw [d.outside id different]; exact h.object⟩

def parameterIds (base : Nat) : Var→Nat
  | .a=>base | .n=>base+1 | .j=>base+2

/-- The source's two parameters and local j are actually allocated and
initialized, with no pre-existing Locals/View assumption. -/
theorem initialize_parameters {F : Type} {entry : State F}
    {object length : Nat} (well : WellScoped entry) (host : entry.mode=.host)
    (emptyEnv : entry.environment=[])
    (buffer : entry.objects object=some (zeroPrefixObject length 0)) (fits : length<2^64) :
    ∃aState nState jState,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object 0)))=some aState ∧
      aState.declare .u64 "n" (some (.integer (integer64 length)))=some nState ∧
      nState.declare .u64 "j" (some (.integer (integer64 0)))=some jState ∧
      View jState object length entry.scope (parameterIds entry.nextObject) 0 := by
  obtain ⟨aState,da⟩ := declare_exists well _ "a" _ (pointer_storable object)
  have wa:=wellScoped_declare well da
  obtain ⟨nState,dn⟩ := declare_exists wa _ "n" _ (u64_storable length fits)
  have wn:=wellScoped_declare wa dn
  obtain ⟨jState,dj⟩ := declare_exists wn _ "j" _ (u64_storable 0 (by norm_num))
  have ia:=declare_storable (pointer_storable object) (pointer_storable object).converted da
  have inn:=declare_storable (u64_storable length fits) (u64_storable length fits).converted dn
  have ij:=declare_storable (u64_storable 0 (by norm_num)) (u64_storable 0 (by norm_num)).converted dj
  have oa:=ia.nextObject
  have onn:=inn.nextObject
  have sa:=ia.scope
  have sn:=inn.scope
  have old : object<entry.nextObject := well.objectIds _ _ buffer
  have sepA : object≠entry.nextObject := by omega
  have sepN : object≠aState.nextObject := by omega
  have sepJ : object≠nState.nextObject := by omega
  have hlocals : Locals jState name type (parameterIds entry.nextObject) entry.scope
      (value object length 0) := by
    constructor
    · intro v
      cases v <;> simp [parameterIds,name,type,ij.environment,inn.environment,
        ia.environment,emptyEnv,oa,onn,scalarPointer,List.lookup]
    · intro v
      cases v with
      | a =>
        have ha:=slot_declare_other ia.slot inn (by omega)
        have haj:=slot_declare_other ha ij (by omega)
        simpa only [parameterIds,type,value] using haj
      | n =>
        have hn:=slot_declare_other inn.slot ij (by omega)
        simpa only [parameterIds,type,value,oa,sa] using hn
      | j =>
        simpa only [parameterIds,type,value,oa,onn,sa,sn] using ij.slot
    · intro v w he
      cases v <;> cases w <;> simp_all [parameterIds] <;> omega
    · rw [ij.nextScope,inn.nextScope,ia.nextScope]
      exact well.current
  refine ⟨aState,nState,jState,da,dn,dj,?_,?_,hlocals,?_,wellScoped_declare wn dj,by omega,fits⟩
  · exact ij.mode.trans (inn.mode.trans (ia.mode.trans host))
  · rw [ij.outside object sepJ,inn.outside object sepN,ia.outside object sepA]
    exact buffer
  · intro v
    cases v <;> simp only [parameterIds] <;> omega

#print axioms declare_exists
#print axioms initialize_parameters
end RH080Next.FFTPV.ZeroFrame
