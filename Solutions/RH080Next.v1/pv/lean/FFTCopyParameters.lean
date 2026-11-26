/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTCopyLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.CopyLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

theorem pointer_storable (object start : Nat) :
    Storable (.pointer .u64) (.pointer (wordPointer object start)) := by
  have hb : (Value.pointer (wordPointer object start)).byteSize = 8 := stored_pointer_width _
  exact ⟨by rw [hb]; rfl, by rw [hb]; decide, by rfl⟩

private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue)
    (d : Declaration before after cname newtype newvalue)
    (different : id ≠ before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable, by rw [d.outside id different]; exact h.object⟩

def parameterIds (base : Nat) : Var → Nat
  | .output => base | .input => base+1 | .n => base+2 | .j => base+3

/-- Actual declaration of both pointer parameters, the length parameter, and
local j. The initial typed memory is an explicit caller precondition; the
application's parameter binding and local initialization are proved. -/
theorem initialize_parameters {F : Type} {entry : State F}
    {outObject outLength outStart inObject inLength inStart length : Nat}
    {old input : Nat → Nat}
    (well : WellScoped entry) (emptyEnv : entry.environment = [])
    (outRep : WordArrayRep entry outObject outLength old)
    (inRep : WordArrayRep entry inObject inLength input)
    (shape : inObject = outObject → inLength = outLength)
    (ranges : outObject ≠ inObject ∨ outStart = inStart ∨ outStart+length ≤ inStart ∨ inStart+length ≤ outStart)
    (outBound : outStart+length ≤ outLength) (inBound : inStart+length ≤ inLength)
    (fits : length < 2^64) :
    ∃outState inState nState jState,
      entry.declare (.pointer .u64) "out" (some (.pointer (wordPointer outObject outStart))) = some outState ∧
      outState.declare (.pointer .u64) "in" (some (.pointer (wordPointer inObject inStart))) = some inState ∧
      inState.declare .u64 "n" (some (.integer (integer64 length))) = some nState ∧
      nState.declare .u64 "j" (some (.integer (integer64 0))) = some jState ∧
      View jState outObject outLength outStart inObject inLength inStart length entry.scope
        (parameterIds entry.nextObject) old (fun i => input (inStart+i)) 0 := by
  obtain ⟨outState, dout⟩ := ZeroFrame.declare_exists well _ "out" _ (pointer_storable outObject outStart)
  have wo := wellScoped_declare well dout
  obtain ⟨inState, din⟩ := ZeroFrame.declare_exists wo _ "in" _ (pointer_storable inObject inStart)
  have wi := wellScoped_declare wo din
  obtain ⟨nState, dn⟩ := ZeroFrame.declare_exists wi _ "n" _ (ZeroFrame.u64_storable length fits)
  have wn := wellScoped_declare wi dn
  obtain ⟨jState, dj⟩ := ZeroFrame.declare_exists wn _ "j" _ (ZeroFrame.u64_storable 0 (by norm_num))
  have io := declare_storable (pointer_storable outObject outStart) (pointer_storable outObject outStart).converted dout
  have ii := declare_storable (pointer_storable inObject inStart) (pointer_storable inObject inStart).converted din
  have inn := declare_storable (ZeroFrame.u64_storable length fits) (ZeroFrame.u64_storable length fits).converted dn
  have ij := declare_storable (ZeroFrame.u64_storable 0 (by norm_num)) (ZeroFrame.u64_storable 0 (by norm_num)).converted dj
  have oo := io.nextObject
  have oi := ii.nextObject
  have onn := inn.nextObject
  have so := io.scope
  have si := ii.scope
  have sn := inn.scope
  have oldOut : outObject < entry.nextObject := well.objectIds _ _ outRep.2.1
  have oldIn : inObject < entry.nextObject := well.objectIds _ _ inRep.2.1
  have hlocals : Locals jState name type (parameterIds entry.nextObject) entry.scope
      (value outObject outStart inObject inStart length 0) := by
    constructor
    · intro v
      cases v <;> simp [parameterIds, name, type, ij.environment, inn.environment,
        ii.environment, io.environment, emptyEnv, oo, oi, onn, scalarPointer, List.lookup]
    · intro v
      cases v with
      | output =>
        have h1 := slot_declare_other io.slot ii (by omega)
        have h2 := slot_declare_other h1 inn (by omega)
        have h3 := slot_declare_other h2 ij (by omega)
        simpa only [parameterIds, type, value] using h3
      | input =>
        have h1 := slot_declare_other ii.slot inn (by omega)
        have h2 := slot_declare_other h1 ij (by omega)
        simpa only [parameterIds, type, value, oo, so] using h2
      | n =>
        have h1 := slot_declare_other inn.slot ij (by omega)
        simpa only [parameterIds, type, value, oo, oi, so, si] using h1
      | j =>
        simpa only [parameterIds, type, value, oo, oi, onn, so, si, sn] using ij.slot
    · intro v w he
      cases v <;> cases w <;> simp_all [parameterIds] <;> omega
    · rw [ij.nextScope, inn.nextScope, ii.nextScope, io.nextScope]
      exact well.current
  have outPresent : jState.objects outObject = some (wordObject outLength old) := by
    rw [ij.outside outObject (by omega), inn.outside outObject (by omega),
      ii.outside outObject (by omega), io.outside outObject (by omega)]
    exact outRep.2.1
  have inPresent : jState.objects inObject = some (wordObject inLength input) := by
    rw [ij.outside inObject (by omega), inn.outside inObject (by omega),
      ii.outside inObject (by omega), io.outside inObject (by omega)]
    exact inRep.2.1
  have host : jState.mode = .host := ij.mode.trans (inn.mode.trans (ii.mode.trans (io.mode.trans outRep.1)))
  refine ⟨outState, inState, nState, jState, dout, din, dn, dj,
    host, ?_, ⟨input, ⟨host, inPresent, inRep.2.2⟩, fun i hi => rfl⟩,
    hlocals, ?_, shape, ranges, outBound, inBound, wellScoped_declare wn dj, by omega, fits⟩
  · simpa only [prefixData_zero] using (show WordArrayRep jState outObject outLength old from ⟨host, outPresent, outRep.2.2⟩)
  · intro v
    cases v <;> simp only [parameterIds] <;> omega

#print axioms initialize_parameters
end RH080Next.FFTPV.CopyLoop
