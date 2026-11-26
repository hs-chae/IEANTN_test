/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroParameters
import ExplicitApplicationBirthFrame
import FFTRecursiveAST
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.RecursiveSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings ApplicationBirthFrame

inductive Var where | output | start | input | index | step | twiddle | n | total | work deriving DecidableEq

def name : Var → String
  | .output => "output"
  | .start => "start"
  | .input => "input"
  | .index => "index"
  | .step => "step"
  | .twiddle => "twiddle"
  | .n => "n"
  | .total => "total"
  | .work => "work"

def type : Var → CType
  | .output => .pointer .u64
  | .start => .u64
  | .input => .pointer .u64
  | .index => .u64
  | .step => .u64
  | .twiddle => .pointer .u64
  | .n => .u64
  | .total => .u64
  | .work => .pointer .u64

def value (outObj inObj twiddleObj workObj start index step n total : Nat) : Var → Value
  | .output => .pointer (wordPointer outObj 0)
  | .start => .integer (integer64 start)
  | .input => .pointer (wordPointer inObj 0)
  | .index => .integer (integer64 index)
  | .step => .integer (integer64 step)
  | .twiddle => .pointer (wordPointer twiddleObj 0)
  | .n => .integer (integer64 n)
  | .total => .integer (integer64 total)
  | .work => .pointer (wordPointer workObj 0)

def ids (base : Nat) : Var → Nat
  | .output => base+0
  | .start => base+1
  | .input => base+2
  | .index => base+3
  | .step => base+4
  | .twiddle => base+5
  | .n => base+6
  | .total => base+7
  | .work => base+8

def arguments (outObj inObj twiddleObj workObj start index step n total : Nat) : List Value :=
  [.pointer (wordPointer outObj 0),
   .integer (integer64 start),
   .pointer (wordPointer inObj 0),
   .integer (integer64 index),
   .integer (integer64 step),
   .pointer (wordPointer twiddleObj 0),
   .integer (integer64 n),
   .integer (integer64 total),
   .pointer (wordPointer workObj 0)]

/-- The actual nine mixed pointer/scalar parameters are declared and bound
from an arbitrary well-scoped caller entry. No initialized local state,
allocator result, source output or favorable execution is assumed. -/
theorem initialize_parameters {F : Type} {entry : State F}
    (outObj inObj twiddleObj workObj start index step n total : Nat)
    (well : WellScoped entry) (empty : entry.environment = [])
    (hstart : start < 2^64)
    (hindex : index < 2^64)
    (hstep : step < 2^64)
    (hn : n < 2^64)
    (htotal : total < 2^64)
    : ∃after, bindParameters entry FFTRecursivePV.fft_recursive_ast.parameters
      (arguments outObj inObj twiddleObj workObj start index step n total) = some after ∧
      Locals after name type (ids entry.nextObject) entry.scope (value outObj inObj twiddleObj workObj start index step n total) ∧
      Declarations entry after ∧ WellScoped after ∧
      after.nextObject = entry.nextObject+9 ∧ after.scope = entry.scope ∧
      after.nextScope = entry.nextScope := by
  obtain ⟨s0,declared0⟩ := ZeroFrame.declare_exists well (.pointer .u64) "output" (.pointer (wordPointer outObj 0)) (ZeroFrame.pointer_storable outObj)
  have w0 := wellScoped_declare well declared0
  have d0 : Declaration entry s0 "output" (.pointer .u64) (.pointer (wordPointer outObj 0)) :=
    declare_storable (ZeroFrame.pointer_storable outObj) (ZeroFrame.pointer_storable outObj).converted declared0
  obtain ⟨s1,declared1⟩ := ZeroFrame.declare_exists w0 (.u64) "start" (.integer (integer64 start)) (ZeroFrame.u64_storable start hstart)
  have w1 := wellScoped_declare w0 declared1
  have d1 : Declaration s0 s1 "start" (.u64) (.integer (integer64 start)) :=
    declare_storable (ZeroFrame.u64_storable start hstart) (ZeroFrame.u64_storable start hstart).converted declared1
  obtain ⟨s2,declared2⟩ := ZeroFrame.declare_exists w1 (.pointer .u64) "input" (.pointer (wordPointer inObj 0)) (ZeroFrame.pointer_storable inObj)
  have w2 := wellScoped_declare w1 declared2
  have d2 : Declaration s1 s2 "input" (.pointer .u64) (.pointer (wordPointer inObj 0)) :=
    declare_storable (ZeroFrame.pointer_storable inObj) (ZeroFrame.pointer_storable inObj).converted declared2
  obtain ⟨s3,declared3⟩ := ZeroFrame.declare_exists w2 (.u64) "index" (.integer (integer64 index)) (ZeroFrame.u64_storable index hindex)
  have w3 := wellScoped_declare w2 declared3
  have d3 : Declaration s2 s3 "index" (.u64) (.integer (integer64 index)) :=
    declare_storable (ZeroFrame.u64_storable index hindex) (ZeroFrame.u64_storable index hindex).converted declared3
  obtain ⟨s4,declared4⟩ := ZeroFrame.declare_exists w3 (.u64) "step" (.integer (integer64 step)) (ZeroFrame.u64_storable step hstep)
  have w4 := wellScoped_declare w3 declared4
  have d4 : Declaration s3 s4 "step" (.u64) (.integer (integer64 step)) :=
    declare_storable (ZeroFrame.u64_storable step hstep) (ZeroFrame.u64_storable step hstep).converted declared4
  obtain ⟨s5,declared5⟩ := ZeroFrame.declare_exists w4 (.pointer .u64) "twiddle" (.pointer (wordPointer twiddleObj 0)) (ZeroFrame.pointer_storable twiddleObj)
  have w5 := wellScoped_declare w4 declared5
  have d5 : Declaration s4 s5 "twiddle" (.pointer .u64) (.pointer (wordPointer twiddleObj 0)) :=
    declare_storable (ZeroFrame.pointer_storable twiddleObj) (ZeroFrame.pointer_storable twiddleObj).converted declared5
  obtain ⟨s6,declared6⟩ := ZeroFrame.declare_exists w5 (.u64) "n" (.integer (integer64 n)) (ZeroFrame.u64_storable n hn)
  have w6 := wellScoped_declare w5 declared6
  have d6 : Declaration s5 s6 "n" (.u64) (.integer (integer64 n)) :=
    declare_storable (ZeroFrame.u64_storable n hn) (ZeroFrame.u64_storable n hn).converted declared6
  obtain ⟨s7,declared7⟩ := ZeroFrame.declare_exists w6 (.u64) "total" (.integer (integer64 total)) (ZeroFrame.u64_storable total htotal)
  have w7 := wellScoped_declare w6 declared7
  have d7 : Declaration s6 s7 "total" (.u64) (.integer (integer64 total)) :=
    declare_storable (ZeroFrame.u64_storable total htotal) (ZeroFrame.u64_storable total htotal).converted declared7
  obtain ⟨s8,declared8⟩ := ZeroFrame.declare_exists w7 (.pointer .u64) "work" (.pointer (wordPointer workObj 0)) (ZeroFrame.pointer_storable workObj)
  have w8 := wellScoped_declare w7 declared8
  have d8 : Declaration s7 s8 "work" (.pointer .u64) (.pointer (wordPointer workObj 0)) :=
    declare_storable (ZeroFrame.pointer_storable workObj) (ZeroFrame.pointer_storable workObj).converted declared8
  have v0at1 := slot_declare_old w0 (d0.slot) d1
  have v0at2 := slot_declare_old w1 (v0at1) d2
  have v0at3 := slot_declare_old w2 (v0at2) d3
  have v0at4 := slot_declare_old w3 (v0at3) d4
  have v0at5 := slot_declare_old w4 (v0at4) d5
  have v0at6 := slot_declare_old w5 (v0at5) d6
  have v0at7 := slot_declare_old w6 (v0at6) d7
  have v0at8 := slot_declare_old w7 (v0at7) d8
  have v1at2 := slot_declare_old w1 (d1.slot) d2
  have v1at3 := slot_declare_old w2 (v1at2) d3
  have v1at4 := slot_declare_old w3 (v1at3) d4
  have v1at5 := slot_declare_old w4 (v1at4) d5
  have v1at6 := slot_declare_old w5 (v1at5) d6
  have v1at7 := slot_declare_old w6 (v1at6) d7
  have v1at8 := slot_declare_old w7 (v1at7) d8
  have v2at3 := slot_declare_old w2 (d2.slot) d3
  have v2at4 := slot_declare_old w3 (v2at3) d4
  have v2at5 := slot_declare_old w4 (v2at4) d5
  have v2at6 := slot_declare_old w5 (v2at5) d6
  have v2at7 := slot_declare_old w6 (v2at6) d7
  have v2at8 := slot_declare_old w7 (v2at7) d8
  have v3at4 := slot_declare_old w3 (d3.slot) d4
  have v3at5 := slot_declare_old w4 (v3at4) d5
  have v3at6 := slot_declare_old w5 (v3at5) d6
  have v3at7 := slot_declare_old w6 (v3at6) d7
  have v3at8 := slot_declare_old w7 (v3at7) d8
  have v4at5 := slot_declare_old w4 (d4.slot) d5
  have v4at6 := slot_declare_old w5 (v4at5) d6
  have v4at7 := slot_declare_old w6 (v4at6) d7
  have v4at8 := slot_declare_old w7 (v4at7) d8
  have v5at6 := slot_declare_old w5 (d5.slot) d6
  have v5at7 := slot_declare_old w6 (v5at6) d7
  have v5at8 := slot_declare_old w7 (v5at7) d8
  have v6at7 := slot_declare_old w6 (d6.slot) d7
  have v6at8 := slot_declare_old w7 (v6at7) d8
  have v7at8 := slot_declare_old w7 (d7.slot) d8
  have locals : Locals s8 name type (ids entry.nextObject) entry.scope (value outObj inObj twiddleObj workObj start index step n total) := by
    refine ⟨?_,?_,?_,?_⟩
    · intro v; cases v <;> rw [d8.environment,d7.environment,d6.environment,d5.environment,d4.environment,d3.environment,d2.environment,d1.environment,d0.environment,empty] <;>
        simp [name,type,ids,d7.nextObject,d6.nextObject,d5.nextObject,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,List.lookup,Nat.add_assoc]
    · intro v; cases v
      · simpa only [ids,type,value,Nat.add_zero] using v0at8
      · simpa only [ids,type,value,d0.nextObject,d0.scope,Nat.add_assoc,Nat.add_zero] using v1at8
      · simpa only [ids,type,value,d1.nextObject,d0.nextObject,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v2at8
      · simpa only [ids,type,value,d2.nextObject,d1.nextObject,d0.nextObject,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v3at8
      · simpa only [ids,type,value,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,d3.scope,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v4at8
      · simpa only [ids,type,value,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,d4.scope,d3.scope,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v5at8
      · simpa only [ids,type,value,d5.nextObject,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,d5.scope,d4.scope,d3.scope,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v6at8
      · simpa only [ids,type,value,d6.nextObject,d5.nextObject,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,d6.scope,d5.scope,d4.scope,d3.scope,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using v7at8
      · simpa only [ids,type,value,d7.nextObject,d6.nextObject,d5.nextObject,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject,d7.scope,d6.scope,d5.scope,d4.scope,d3.scope,d2.scope,d1.scope,d0.scope,Nat.add_assoc,Nat.add_zero] using d8.slot
    · intro v w same; cases v <;> cases w <;> simp_all [ids] <;> omega
    · rw [d8.nextScope,d7.nextScope,d6.nextScope,d5.nextScope,d4.nextScope,d3.nextScope,d2.nextScope,d1.nextScope,d0.nextScope]; exact well.current
  have bound : bindParameters entry FFTRecursivePV.fft_recursive_ast.parameters
      (arguments outObj inObj twiddleObj workObj start index step n total) = some s8 := by
    change bindParameters entry [(.pointer .u64,"output"),(.u64,"start"),(.pointer .u64,"input"),(.u64,"index"),(.u64,"step"),(.pointer .u64,"twiddle"),(.u64,"n"),(.u64,"total"),(.pointer .u64,"work")]
      [.pointer (wordPointer outObj 0),.integer (integer64 start),.pointer (wordPointer inObj 0),.integer (integer64 index),.integer (integer64 step),.pointer (wordPointer twiddleObj 0),.integer (integer64 n),.integer (integer64 total),.pointer (wordPointer workObj 0)] = some s8
    simp [bindParameters,declared0,declared1,declared2,declared3,declared4,declared5,declared6,declared7,declared8]
  refine ⟨s8,bound,locals,.cons declared0 (.cons declared1 (.cons declared2 (.cons declared3 (.cons declared4 (.cons declared5 (.cons declared6 (.cons declared7 (.cons declared8 (.nil s8))))))))),w8,?_,?_,?_⟩
  · rw [d8.nextObject,d7.nextObject,d6.nextObject,d5.nextObject,d4.nextObject,d3.nextObject,d2.nextObject,d1.nextObject,d0.nextObject]
  · exact d8.scope.trans (d7.scope.trans (d6.scope.trans (d5.scope.trans (d4.scope.trans (d3.scope.trans (d2.scope.trans (d1.scope.trans (d0.scope))))))))
  · exact d8.nextScope.trans (d7.nextScope.trans (d6.nextScope.trans (d5.nextScope.trans (d4.nextScope.trans (d3.nextScope.trans (d2.nextScope.trans (d1.nextScope.trans (d0.nextScope))))))))

#print axioms initialize_parameters
end RH080Next.FFTPV.RecursiveSource
