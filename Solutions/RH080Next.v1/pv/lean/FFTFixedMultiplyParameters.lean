/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTProductCoreFrames
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplyParameters
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

inductive Var where | output | a | b | work deriving DecidableEq

def name : Var→String | .output=>"out" | .a=>"a" | .b=>"b" | .work=>"work"
def type (_ : Var) : CType:=.pointer .u64
def value (outObj outStart aObj aStart bObj bStart workObj workStart : Nat) : Var→Value
  | .output=>.pointer (wordPointer outObj outStart)
  | .a=>.pointer (wordPointer aObj aStart)
  | .b=>.pointer (wordPointer bObj bStart)
  | .work=>.pointer (wordPointer workObj workStart)
def ids (base : Nat) : Var→Nat | .output=>base | .a=>base+1 | .b=>base+2 | .work=>base+3

theorem pointer_storable (object start : Nat) : Storable (.pointer .u64) (.pointer (wordPointer object start)):=by
  have hb : (Value.pointer (wordPointer object start)).byteSize=8:=stored_pointer_width _
  exact ⟨by rw [hb];rfl,by rw [hb];decide,by rfl⟩

/-- All four actual source parameters are really declared and bound to the
caller argument pointers, at arbitrary slice offsets. No pre-existing
application scalar representation or successful initialization is assumed. -/
theorem initialize_parameters {F : Type} {entry : State F}
    (outObj outStart aObj aStart bObj bStart workObj workStart : Nat)
    (well : WellScoped entry) (empty : entry.environment=[]) :
    ∃after,bindParameters entry fixed_multiply_ast.parameters
      [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
        .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some after ∧
      Locals after name type (ids entry.nextObject) entry.scope
        (value outObj outStart aObj aStart bObj bStart workObj workStart) ∧
      Declarations entry after ∧ WellScoped after ∧ after.nextObject=entry.nextObject+4 ∧
      after.scope=entry.scope ∧ after.nextScope=entry.nextScope := by
  obtain ⟨outState,outDeclared⟩:=ZeroFrame.declare_exists well _ "out" _ (pointer_storable outObj outStart)
  have outW:=wellScoped_declare well outDeclared
  have dout : Declaration entry outState "out" (.pointer .u64) (.pointer (wordPointer outObj outStart)):=
    declare_storable (pointer_storable outObj outStart) (pointer_storable outObj outStart).converted outDeclared
  obtain ⟨aState,aDeclared⟩:=ZeroFrame.declare_exists outW _ "a" _ (pointer_storable aObj aStart)
  have aW:=wellScoped_declare outW aDeclared
  have da : Declaration outState aState "a" (.pointer .u64) (.pointer (wordPointer aObj aStart)):=
    declare_storable (pointer_storable aObj aStart) (pointer_storable aObj aStart).converted aDeclared
  obtain ⟨bState,bDeclared⟩:=ZeroFrame.declare_exists aW _ "b" _ (pointer_storable bObj bStart)
  have bW:=wellScoped_declare aW bDeclared
  have db : Declaration aState bState "b" (.pointer .u64) (.pointer (wordPointer bObj bStart)):=
    declare_storable (pointer_storable bObj bStart) (pointer_storable bObj bStart).converted bDeclared
  obtain ⟨after,workDeclared⟩:=ZeroFrame.declare_exists bW _ "work" _ (pointer_storable workObj workStart)
  have dw : Declaration bState after "work" (.pointer .u64) (.pointer (wordPointer workObj workStart)):=
    declare_storable (pointer_storable workObj workStart) (pointer_storable workObj workStart).converted workDeclared
  have outA:=slot_declare_old outW dout.slot da
  have outB:=slot_declare_old aW outA db
  have outFinal:=slot_declare_old bW outB dw
  have aB:=slot_declare_old aW da.slot db
  have aFinal:=slot_declare_old bW aB dw
  have bFinal:=slot_declare_old bW db.slot dw
  have locals : Locals after name type (ids entry.nextObject) entry.scope
      (value outObj outStart aObj aStart bObj bStart workObj workStart):=by
    refine ⟨?_,?_,?_,?_⟩
    · intro v;cases v <;> rw [dw.environment,db.environment,da.environment,dout.environment,empty] <;>
        simp [name,type,ids,db.nextObject,da.nextObject,dout.nextObject,List.lookup]
    · intro v;cases v
      · exact outFinal
      · simpa only [ids,type,value,dout.nextObject,dout.scope] using aFinal
      · simpa only [ids,type,value,da.nextObject,dout.nextObject,da.scope,dout.scope,Nat.add_assoc] using bFinal
      · simpa only [ids,type,value,db.nextObject,da.nextObject,dout.nextObject,db.scope,da.scope,dout.scope,Nat.add_assoc] using dw.slot
    · intro v w same;cases v <;> cases w <;> simp_all [ids] <;> omega
    · rw [dw.nextScope,db.nextScope,da.nextScope,dout.nextScope];exact well.current
  have params : bindParameters entry fixed_multiply_ast.parameters
      [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
        .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some after:=by
    change bindParameters entry [(.pointer .u64,"out"),(.pointer .u64,"a"),(.pointer .u64,"b"),(.pointer .u64,"work")]
      [.pointer (wordPointer outObj outStart),.pointer (wordPointer aObj aStart),
        .pointer (wordPointer bObj bStart),.pointer (wordPointer workObj workStart)]=some after
    simp [bindParameters,outDeclared,aDeclared,bDeclared,workDeclared]
  refine ⟨after,params,locals,.cons outDeclared (.cons aDeclared (.cons bDeclared (.cons workDeclared (.nil after)))),
    wellScoped_declare bW workDeclared,?_,?_,?_⟩
  · rw [dw.nextObject,db.nextObject,da.nextObject,dout.nextObject]
  · exact dw.scope.trans (db.scope.trans (da.scope.trans dout.scope))
  · exact dw.nextScope.trans (db.nextScope.trans (da.nextScope.trans dout.nextScope))

#print axioms initialize_parameters
end RH080Next.FFTPV.MultiplyParameters
