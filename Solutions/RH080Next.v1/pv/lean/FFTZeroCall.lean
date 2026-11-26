/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTZeroLoop
import FFTSource
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ZeroLoop
open GoldbachDirect GoldbachDirect.Semantics WordArrays

/-- Explicit caller memory before entering the actual helper: a byte-zeroed
host buffer only. No typed-word initial application representation is assumed. -/
def callerState (n : Nat) : State Unit :=
  {environment:=[],objects:=fun key=>if key=0 then some (zeroPrefixObject n 0) else none,
   nextObject:=1,scope:=0,nextScope:=1,foreign:=()}


def emptyCaller : State Unit :=
  {environment:=[],objects:=fun _=>none,nextObject:=0,scope:=0,nextScope:=1,foreign:=()}

/-- The canonical caller state is obtained from generic calloc byte birth,
without assuming the application's typed-word representation. -/
theorem caller_byte_birth (n : Nat) :
    emptyCaller.allocate .host (8*n) (PlatformMemory.zeroBytes (8*n))=
      some (⟨0,0,.void⟩,callerState n) := by
  simp [State.allocate,emptyCaller,callerState,zeroPrefix_zero]
  rfl

def aState (n : Nat) : State Unit :=
  {environment:=[("a",⟨1,0,.pointer .u64⟩)],
   objects:=fun key=>if key=0 then some (zeroPrefixObject n 0)
     else if key=1 then some automaticPointer else none,
   nextObject:=2,scope:=1,nextScope:=2,foreign:=()}

def parameterState (n : Nat) : State Unit :=
  {environment:=[("n",wordPointer 2 0),("a",⟨1,0,.pointer .u64⟩)],
   objects:=fun key=>if key=0 then some (zeroPrefixObject n 0)
     else if key=1 then some automaticPointer
     else if key=2 then some (automaticWord n) else none,
   nextObject:=3,scope:=1,nextScope:=2,foreign:=()}

private theorem declare_a (n : Nat) :
    { (callerState n).enterScope with environment:=[] }.declare
      (.pointer .u64) "a" (some (.pointer (wordPointer 0 0)))=some (aState n) := by
  simp [State.declare,State.allocate,State.store,callerState,aState,State.enterScope,
    automaticPointer,CType.byteSize,State.accessible,Value.convert,CType.integer,wordPointer]
  funext key
  by_cases h0 : key=0
  · simp [h0]
  by_cases h1 : key=1
  · simp [h1]
  · simp [h0,h1]

private theorem declare_n (n : Nat) (hn : n<2^64) :
    (aState n).declare .u64 "n" (some (.integer (integer64 n)))=some (parameterState n) := by
  simp [State.declare,State.allocate,State.store,aState,parameterState,
    automaticWord,wordObject,CType.byteSize,State.accessible,convert64 n hn,wordPointer]
  funext key
  by_cases h0 : key=0
  · simp [h0]
  by_cases h1 : key=1
  · simp [h1]
  by_cases h2 : key=2
  · simp [h2]
    funext offset
    have h : (offset%8=0 ∧ offset<8) ↔ offset=0 := by omega
    simp only [h]
  · simp [h0,h1,h2]

private theorem declare_j (n : Nat) :
    (parameterState n).declare .u64 "j" (some (.integer (integer64 0)))=
      some (loopState n 0 1 2) := by
  simp [State.declare,State.allocate,State.store,parameterState,loopState,frameState,
    automaticWord,wordObject,CType.byteSize,State.accessible,convert64 0 (by norm_num),wordPointer]
  funext key
  by_cases h0 : key=0
  · simp [h0]
  by_cases h1 : key=1
  · simp [h1]
  by_cases h2 : key=2
  · simp [h2]
  by_cases h3 : key=3
  · simp [h3]
    funext offset
    have h : (offset%8=0 ∧ offset<8) ↔ offset=0 := by omega
    simp only [h]
  · simp [h0,h1,h2,h3]


def zeroArgs (n : Nat) : List Value := [.pointer (wordPointer 0 0),.integer (integer64 n)]
def finalState (n : Nat) : State Unit :=
  {(loopState n n 1 (2+n)).leaveScope 1 [] with scope:=0}

private theorem bind_actual_parameters (n : Nat) (hn : n<2^64) :
    bindParameters {(callerState n).enterScope with environment:=[]}
      zero_words_ast.parameters (zeroArgs n)=some (parameterState n) := by
  change (do let a ← {(callerState n).enterScope with environment:=[]}.declare
                (.pointer .u64) "a" (some (.pointer (wordPointer 0 0)))
             let p ← a.declare .u64 "n" (some (.integer (integer64 n)))
             pure p)=_
  rw [declare_a]
  change (aState n).declare .u64 "n" (some (.integer (integer64 n)))=_
  exact declare_n n hn

/-- The complete actual source helper call: parameter allocation, application
local initialization, every source-loop iteration, return conversion and scope
exit. The caller frame is explicit rather than assumed correct or omitted. -/
theorem zero_words_call (context : Context Unit)
    (selected : findFunction context.program "zero_words"=some zero_words_ast)
    (n : Nat) (hn : n<2^64) :
    Call context "zero_words" (zeroArgs n) (callerState n)
      (.value (.integer (integer64 0))) (finalState n) := by
  apply Call.internal (function:=zero_words_ast)
    (entered:=parameterState n) (middle:=loopState n n 1 (2+n))
    selected loop_is_actual (bind_actual_parameters n hn)
  · apply Body.finish
    · exact .cons (.declareSome
        (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl))
        (declare_j n))
        (.cons (loop_execution context n n 0 2 (by omega) hn (by omega))
          (.abrupt (.returnSome (.literal (.integer 0 "ULL") _
            (.integer (integer64 0)) (by rfl))) (by intro h; cases h)))
    · intro label h
      cases h
  · exact convert64 0 (by norm_num)
  · rfl

/-- Initial byte-zero allocation is refined to actual initialized uint64 words
by the source function; initial typed application contents are not trusted. -/
theorem final_word_representation (n : Nat) :
    WordArrayRep (finalState n) 0 n (fun _=>0) := by
  refine ⟨by rfl,?_,fun i hi=>by norm_num⟩
  simp [finalState,State.leaveScope,loopState,frameState,zeroPrefix_full,wordObject]


def sourceContext : Context Unit :=
  {program:=FFTPV.program,foreign:=fun _ _ _ _ _=>False,
   headerConstant:=fun _=>none,builtin:=fun _ _=>none}

/-- Completed source-first verification of this actual application helper.
It states a canonical allocated caller frame; it does not assert arbitrary
caller-frame refinement or correctness of the complete numerical FFT program. -/
theorem source_zero_words_execution (n : Nat) (hn : n<2^64) :
    GoldbachDirect.Correspondence.SourceSyntaxCorresponds FFTPV.source FFTPV.program ∧
    Call sourceContext "zero_words" (zeroArgs n) (callerState n)
      (.value (.integer (integer64 0))) (finalState n) ∧
    WordArrayRep (finalState n) 0 n (fun _=>0) :=
  ⟨actual_source_syntax,zero_words_call sourceContext (by rfl) n hn,
    final_word_representation n⟩

#print axioms source_zero_words_execution

#print axioms bind_actual_parameters
#print axioms zero_words_call
#print axioms final_word_representation

#print axioms declare_a
#print axioms declare_n
#print axioms declare_j
end RH080Next.FFTPV.ZeroLoop
