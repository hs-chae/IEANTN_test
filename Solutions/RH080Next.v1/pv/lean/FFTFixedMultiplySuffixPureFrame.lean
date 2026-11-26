/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTFixedMultiplySuffixFrame
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.MultiplySuffix
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots ProductInner ApplicationBirthFrame

private theorem list_head {F : Type} {context : Context F} {before after : State F} {s : Stmt} {ss : List Stmt}
    (run : ExecList context before (s::ss) .normal after) :
    ∃middle,Exec context before s .normal middle ∧ ExecList context middle ss .normal after := by
  cases run with
  | cons head tail => exact ⟨_,head,tail⟩
  | abrupt run ne => exact False.elim (ne rfl)

/-- Actual separated output pointer and persistent index name, independent of
all changing numerical values and fresh temporary locals. -/
structure PrefixTrack {F : Type} (state : State F) (outObj outStart outId outOwner iId : Nat) : Prop where
  namedOut : state.environment.lookup "out"=some (scalarPointer outId (.pointer .u64))
  outputSlot : Slot state outId outOwner (.pointer .u64) (.pointer (wordPointer outObj outStart))
  namedI : state.environment.lookup "i"=some (scalarPointer iId .u64)
  different : outId≠iId
  separated : outId≠outObj
  well : WellScoped state

private theorem zero_declaration {F : Type} {context : Context F} {before after : State F} {cname : String}
    {outObj outStart outId outOwner iId cutoff : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId)
    (differentOut : "out"≠cname) (differentI : "i"≠cname) (writes : List Nat) (fresh : cutoff ≤ before.nextObject)
    (run : Exec context before (.declare .u64 cname (some (lit 0))) .normal after) :
    Declaration before after cname .u64 (.integer (integer64 0)) ∧
      PrefixTrack after outObj outStart outId outOwner iId ∧ Frame cutoff before after writes := by
  cases run with | declareSome er decl =>
    have known : Eval context before (lit 0) (.integer (integer64 0)) before :=
      .literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)
    obtain ⟨eq,state⟩:=PureDeterminism.eval_unique (by trivial) known er
    cases eq;cases state
    have st:=ZeroFrame.u64_storable 0 (by norm_num)
    have d:=declare_storable st st.converted decl
    refine ⟨d,⟨?_,ApplicationBirthFrame.slot_declare_old h.well h.outputSlot d,?_,h.different,h.separated,
      wellScoped_declare h.well decl⟩,ApplicationBirthFrame.declare_frame cutoff writes h.well fresh decl⟩
    · rw [d.environment]
      simpa [List.lookup,show ("out"==cname)=false from by simp [differentOut]] using h.namedOut
    · rw [d.environment]
      simpa [List.lookup,show ("i"==cname)=false from by simp [differentI]] using h.namedI

/-- Narrow a declaration-free checked source frame into the fixed caller cutoff. -/
private theorem tracked_step {F : Type} {context : Context F} {before after : State F} {stmt : Stmt}
    {outObj outStart outId outOwner iId cutoff : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId)
    (locals : List (String × Pointer)) (arrays : List SourceArrayFrame.ArrayBinding)
    (bindings : SourceArrayFrame.Bindings before locals arrays)
    (only : SourceArrayFrame.Only locals arrays stmt) (noAlloc : SourceNoAlloc.Only stmt)
    (writes : List Nat) (fresh : cutoff ≤ before.nextObject)
    (allowed : ∀id∈SourceArrayFrame.writes locals arrays,id∈writes ∨ cutoff ≤ id)
    (protect : outId∉SourceArrayFrame.writes locals arrays)
    (run : Exec context before stmt .normal after) :
    PrefixTrack after outObj outStart outId outOwner iId ∧ Frame cutoff before after writes := by
  have effect:=SourceNoAlloc.exec_effect run noAlloc h.well
  have scan:=SourceArrayFrame.exec_frame run only noAlloc h.well bindings
  refine ⟨⟨by rw [effect.environment];exact h.namedOut,
    slot_scan_frame h.outputSlot scan protect,by rw [effect.environment];exact h.namedI,
    h.different,h.separated,effect.well⟩,
    ⟨effect.well,by rwa [effect.nextObject],by rw [effect.nextObject],effect.nextScope,effect.mode,effect.foreign,?_⟩⟩
  intro id old absent
  apply scan.outside id
  intro member
  rcases allowed id member with yes | born
  · exact absent yes
  · omega

private theorem index_bindings {F : Type} {state : State F} {outObj outStart outId outOwner iId : Nat}
    (h : PrefixTrack state outObj outStart outId outOwner iId) :
    SourceArrayFrame.Bindings state [("i",scalarPointer iId .u64)] [] := by
  constructor
  · intro name pointer member
    simp only [List.mem_singleton,Prod.mk.injEq] at member
    rcases member with ⟨rfl,rfl⟩;exact h.namedI
  · intro item member;cases member
  · intro item member;cases member

private theorem index_reset_frame {F : Type} {context : Context F} {before after : State F}
    {outObj outStart outId outOwner iId cutoff : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId) (fresh : cutoff ≤ before.nextObject)
    (run : Exec context before resetIndex .normal after) :
    PrefixTrack after outObj outStart outId outOwner iId ∧ Frame cutoff before after [outObj,iId] := by
  apply tracked_step h [("i",scalarPointer iId .u64)] [] (index_bindings h)
    (by simp [resetIndex,v,lit,SourceArrayFrame.Only,SourceArrayFrame.Writable])
    (by simp [resetIndex,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]) [outObj,iId] fresh
    (by intro id member;simp [SourceArrayFrame.writes,scalarPointer] at member;subst id;simp)
    (by simpa [SourceArrayFrame.writes,scalarPointer] using h.different) run

private theorem local_branch_frame {F : Type} {context : Context F} {before after : State F}
    {outObj outStart outId outOwner iId signId cutoff : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId)
    (named : before.environment.lookup "sign"=some (scalarPointer signId .u64))
    (fresh : cutoff ≤ before.nextObject) (born : cutoff ≤ signId) (separated : outId≠signId)
    (run : Exec context before signBranch .normal after) :
    PrefixTrack after outObj outStart outId outOwner iId ∧ Frame cutoff before after [outObj,iId] := by
  have bindings : SourceArrayFrame.Bindings before [("sign",scalarPointer signId .u64)] [] := by
    constructor
    · intro name pointer member
      simp only [List.mem_singleton,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩;exact named
    · intro item member;cases member
    · intro item member;cases member
  apply tracked_step h _ _ bindings
    (by simp [signBranch,v,lit,SourceArrayFrame.Only,SourceArrayFrame.Writable])
    (by simp [signBranch,signCondition,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]) [outObj,iId] fresh
    (by intro id member;simp [SourceArrayFrame.writes,scalarPointer] at member;subst id;exact Or.inr born)
    (by simpa [SourceArrayFrame.writes,scalarPointer] using separated) run

/-- Exact actual pure prefix: all old caller objects except output and i are
framed. Fresh sign/lost/overflow slots are real declarations above the cutoff. -/
theorem prefix8_frame {F : Type} {context : Context F} {before after : State F}
    {outObj outStart outId outOwner iId : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId)
    (run : ExecList context before
      [signDeclaration,signBranch,lostDeclaration,resetIndex,lostLoop,resetIndex,copyLoop,signStore]
      .normal after) : Frame before.nextObject before after [outObj,iId] := by
  obtain ⟨s1,r1,rest⟩:=list_head run
  obtain ⟨s2,r2,rest⟩:=list_head rest
  obtain ⟨s3,r3,rest⟩:=list_head rest
  obtain ⟨s4,r4,rest⟩:=list_head rest
  obtain ⟨s5,r5,rest⟩:=list_head rest
  obtain ⟨s6,r6,rest⟩:=list_head rest
  obtain ⟨s7,r7,rest⟩:=list_head rest
  obtain ⟨s8,r8,rest⟩:=list_head rest
  cases rest
  have outOld:=h.well.objectIds _ _ h.outputSlot.object
  obtain ⟨d1,h1,f1⟩:=zero_declaration h (by decide) (by decide) [outObj,iId] (le_refl _) r1
  have signNamed : s1.environment.lookup "sign"=some (scalarPointer before.nextObject .u64) := by simp [d1.environment,List.lookup]
  obtain ⟨h2,f2⟩:=local_branch_frame h1 signNamed f1.fresh (le_refl _) (by omega) r2
  have first:=f1.trans f2
  obtain ⟨d3,h3,f3⟩:=zero_declaration h2 (by decide) (by decide) [outObj,iId] first.fresh r3
  obtain ⟨h4,f4⟩:=index_reset_frame h3 (first.trans f3).fresh r4
  have resetEffect:=SourceNoAlloc.exec_effect r4 (by simp [resetIndex,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]) h3.well
  have lostNamed : s4.environment.lookup "lost"=some (scalarPointer s2.nextObject .u64) := by
    rw [resetEffect.environment,d3.environment];simp [List.lookup]
  have lostBindings : SourceArrayFrame.Bindings s4 [("lost",scalarPointer s2.nextObject .u64),("i",scalarPointer iId .u64)] [] := by
    constructor
    · intro name pointer member
      simp only [List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at member
      rcases member with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact lostNamed
      · exact h4.namedI
    · intro item member;cases member
    · intro item member;cases member
  obtain ⟨h5,f5⟩:=tracked_step h4 _ _ lostBindings
    (by simp [lostLoop,lostBody,lostStore,increment,v,lit,SourceArrayFrame.Only,SourceArrayFrame.Writable])
    (by simp [lostLoop,lostCondition,lostBody,lostStore,lostExpression,increment,v,lit,SourceNoAlloc.Only,SourcePure.CallFree])
    [outObj,iId] (first.trans (f3.trans f4)).fresh
    (by
      intro id member
      simp only [SourceArrayFrame.writes,List.map_cons,List.map_nil,List.append_nil,scalarPointer,List.mem_cons,List.mem_nil_iff,or_false] at member
      rcases member with rfl|rfl
      · exact Or.inr first.fresh
      · exact Or.inl (by simp))
    (by
      simp only [SourceArrayFrame.writes,List.map_cons,List.map_nil,List.append_nil,scalarPointer,List.mem_cons,List.mem_nil_iff,or_false,not_or]
      exact ⟨by have mono:=first.nextObject;omega,h.different⟩) r5
  have five:=first.trans (f3.trans (f4.trans f5))
  obtain ⟨h6,f6⟩:=index_reset_frame h5 five.fresh r6
  let arrays : List SourceArrayFrame.ArrayBinding := [⟨"out",scalarPointer outId (.pointer .u64),wordPointer outObj outStart⟩]
  have arrayBindings : SourceArrayFrame.Bindings s6 [("i",scalarPointer iId .u64)] arrays := by
    constructor
    · exact (index_bindings h6).named
    · intro item member
      simp only [arrays,List.mem_singleton] at member
      subst item
      exact ⟨h6.namedOut,h6.outputSlot.read⟩
    · intro item member
      simp only [arrays,List.mem_singleton] at member
      subst item
      simpa [SourceArrayFrame.writes,arrays,scalarPointer,wordPointer] using And.intro h.different h.separated
  obtain ⟨h7,f7⟩:=tracked_step h6 _ _ arrayBindings
    (by simp [copyLoop,copyBody,copyStore,increment,v,lit,arrays,SourceArrayFrame.Only,SourceArrayFrame.Writable])
    (by simp [copyLoop,copyCondition,copyBody,copyStore,increment,v,lit,SourceNoAlloc.Only,SourcePure.CallFree])
    [outObj,iId] (five.trans f6).fresh
    (by intro id member;simp [SourceArrayFrame.writes,arrays,scalarPointer,wordPointer] at member;rcases member with rfl|rfl <;> simp)
    (by simpa [SourceArrayFrame.writes,arrays,scalarPointer,wordPointer] using And.intro h.different h.separated) r7
  have storeBindings : SourceArrayFrame.Bindings s7 [] arrays := by
    constructor
    · intro name pointer member;cases member
    · intro item member
      simp only [arrays,List.mem_singleton] at member
      subst item
      exact ⟨h7.namedOut,h7.outputSlot.read⟩
    · intro item member
      simp only [arrays,List.mem_singleton] at member
      subst item
      simpa [SourceArrayFrame.writes,arrays,scalarPointer,wordPointer] using h.separated
  obtain ⟨h8,f8⟩:=tracked_step h7 _ _ storeBindings
    (by simp [signStore,v,lit,arrays,SourceArrayFrame.Only,SourceArrayFrame.Writable])
    (by simp [signStore,v,lit,SourceNoAlloc.Only,SourcePure.CallFree]) [outObj,iId] (five.trans (f6.trans f7)).fresh
    (by intro id member;simp [SourceArrayFrame.writes,arrays,wordPointer] at member;subst id;simp)
    (by simpa [SourceArrayFrame.writes,arrays,wordPointer] using h.separated) r8
  have eight:=five.trans (f6.trans (f7.trans f8))
  exact eight

/-- Include the actual final overflow declaration in the pure-prefix frame. -/
theorem prefix_frame {F : Type} {context : Context F} {before after : State F}
    {outObj outStart outId outOwner iId : Nat}
    (h : PrefixTrack before outObj outStart outId outOwner iId)
    (run : ExecList context before
      [signDeclaration,signBranch,lostDeclaration,resetIndex,lostLoop,resetIndex,copyLoop,signStore,overflowDeclaration]
      .normal after) : Frame before.nextObject before after [outObj,iId] := by
  obtain ⟨s1,r1,rest⟩:=list_head run
  obtain ⟨s2,r2,rest⟩:=list_head rest
  obtain ⟨s3,r3,rest⟩:=list_head rest
  obtain ⟨s4,r4,rest⟩:=list_head rest
  obtain ⟨s5,r5,rest⟩:=list_head rest
  obtain ⟨s6,r6,rest⟩:=list_head rest
  obtain ⟨s7,r7,rest⟩:=list_head rest
  obtain ⟨s8,r8,rest⟩:=list_head rest
  obtain ⟨s9,r9,rest⟩:=list_head rest
  cases rest
  have eightRun : ExecList context before
      [signDeclaration,signBranch,lostDeclaration,resetIndex,lostLoop,resetIndex,copyLoop,signStore] .normal s8 :=
    .cons r1 (.cons r2 (.cons r3 (.cons r4 (.cons r5 (.cons r6 (.cons r7 (.cons r8 .nil)))))))
  have eight:=prefix8_frame h eightRun
  have f9 : Frame before.nextObject s8 after [outObj,iId] := by
    cases r9 with | declareSome ev decl =>
      have pure:=SourcePure.eval_state ev (by simp [v,lit,SourcePure.CallFree])
      cases pure
      exact ApplicationBirthFrame.declare_frame _ _ eight.well eight.fresh decl
  exact eight.trans f9

#print axioms prefix8_frame
#print axioms prefix_frame
end RH080Next.FFTPV.MultiplySuffix
