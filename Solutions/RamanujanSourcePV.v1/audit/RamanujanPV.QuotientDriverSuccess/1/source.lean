/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientDriverExecution

/-! Universal successful-driver correctness. Actual source failure returns must
be excluded by the observed modeled return0; no successful-I/O premise is added. -/
namespace RamanujanPV.QuotientDriverSuccess
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open QuotientCMachine QuotientDriverSource QuotientDriverInit QuotientDriverExecution
set_option autoImplicit false
set_option maxHeartbeats 2000000

lemma no_pure_call (heap : Heap) (env : Env) (name : String) (args : List Expr) :
    evalPure QuotientSqrtExecute.noCalls heap env 8 (.call (.var name) args)=none := by
  change (do QuotientSqrtExecute.noCalls name (←args.mapM (evalPure QuotientSqrtExecute.noCalls heap env 7)))=none
  cases h : args.mapM (evalPure QuotientSqrtExecute.noCalls heap env 7) <;> rfl

lemma eval_nat_exact {token n : Nat} {s t : DriverState} {value : DriverValue}
    (run : DriverEval token (.nat n) s t value) :
    ∃ raw, literal n=some raw ∧ t=s ∧ value=.core raw := by
  cases run with
  | pure evaluated =>
    exact ⟨_,(pure_literal QuotientSqrtExecute.noCalls s.heap (coreEnv s.env) 7 n).symm.trans evaluated,rfl,rfl⟩

lemma eval_variable_exact {token : Nat} {name : String} {s t : DriverState}
    {raw : Value} {value : DriverValue}
    (lookup : s.env name=some (.core raw)) (run : DriverEval token (.var name) s t value) :
    t=s ∧ value=.core raw := by
  cases run with
  | pure evaluated =>
    rw [pure_var] at evaluated
    have equal := Option.some.inj ((show coreEnv s.env name=some raw by simp [coreEnv,lookup]).symm.trans evaluated)
    cases equal
    exact ⟨rfl,rfl⟩

lemma counter_arguments_exact {layout : Layout} {token : Nat} {s t : DriverState} {values : List DriverValue}
    (small : s.env "rpc_small"=some (.core (.ptr layout.smallBase)))
    (large : s.env "rpc_large"=some (.core (.ptr layout.largeBase)))
    (run : DriverArgs token [.nat input,.nat capacity,.var "rpc_small",.var "rpc_large"] s t values) :
    t=s ∧ values=[.core (.i64 input),.core (.i32 capacity),.core (.ptr layout.smallBase),.core (.ptr layout.largeBase)] := by
  cases run with
  | cons first rest =>
    obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact first
    have hv : raw=.i64 input := by simpa [literal,input] using (Option.some.inj ((by norm_num [literal,input] : literal input=some (.i64 input)).symm.trans hraw)).symm
    subst raw
    cases rest with
    | cons second rest =>
      obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact second
      have hv : raw=.i32 capacity := (Option.some.inj ((by norm_num [literal,capacity] : literal capacity=some (.i32 capacity)).symm.trans hraw)).symm
      subst raw
      cases rest with
      | cons third rest =>
        obtain ⟨rfl,rfl⟩ := eval_variable_exact small third
        cases rest with
        | cons fourth rest =>
          obtain ⟨rfl,rfl⟩ := eval_variable_exact large fourth
          cases rest
          exact ⟨rfl,rfl⟩

lemma stored_word_read {heap after : Heap} {address index word : Nat}
    (stored : write heap address index word=some after) :
    QuotientCMachine.read after address index=some (.u64 word) := by
  unfold write at stored
  cases hb : heap address with
  | none => simp [hb] at stored
  | some block =>
    rw [hb] at stored
    change (if address%8=0 ∧ index < block.extent ∧ address+8*index+8 ≤ modulus ∧ word < modulus then
      some (Function.update heap address (some {block with words:=Function.update block.words index word}))
      else none)=some after at stored
    split at stored
    · rename_i good
      have same := Option.some.inj stored
      subst after
      apply read_of_block (block:={block with words:=Function.update block.words index word})
        (by simp) good.1 good.2.1 good.2.2.1
      simpa using good.2.2.2
    · contradiction

lemma counter_call_exact {layout : Layout} {token : Nat} {s t : DriverState} {value : DriverValue}
    (small : s.env "rpc_small"=some (.core (.ptr layout.smallBase)))
    (large : s.env "rpc_large"=some (.core (.ptr layout.largeBase)))
    (owned : Owned s.heap) (buffers : QuotientCInit.Buffers s.heap layout.smallBase layout.largeBase input.sqrt)
    (run : DriverEval token counterCall s t value) :
    value=.core (.u64 (Nat.primeCounting input)) ∧ t.env=s.env ∧ t.locations=s.locations ∧
      t.world=s.world ∧ Owned t.heap := by
  change DriverEval token (.call (.var "rpc_quotient_count")
    [.nat input,.nat capacity,.var "rpc_small",.var "rpc_large"]) s t value at run
  cases run with
  | pure evaluated => rw [no_pure_call] at evaluated; contradiction
  | internal arguments converted called post =>
    obtain ⟨rfl,rfl⟩ := counter_arguments_exact small large arguments
    have rawEq : _ = [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] := by
      simpa [coreArguments] using (Option.some.inj converted).symm
    subst_vars
    have result := driver_call_correct_of_buffers layout owned buffers called
    exact ⟨congrArg DriverValue.core result.1,rfl,rfl,rfl,result.2.1⟩

structure ResultRep (token : Nat) (world : World) (s : DriverState) : Prop where
  result : s.env "result"=some (.core (.u64 (Nat.primeCounting input)))
  address : ∃ address, location s "result"=some address ∧
    QuotientCMachine.read s.heap address 0=some (.u64 (Nat.primeCounting input))
  stdout : s.env "stdout"=some (.core (.ptr token))
  sameWorld : s.world=world

lemma declaration_result {layout : Layout} {token : Nat} {world : World} {t : DriverState}
    (run : DriverDeclare token [⟨"uint64_t","result",some counterCall⟩]
      (initialDriver layout token world) t) : ResultRep token world t := by
  cases run with
  | @cons name rhs rest before reserved middle after final raw value address uninitialized written
      uninitializedBound freshName freshLocation freshAddress aligned bounded apart reservedObject
      expression converted valueBound actualStore initialized restRun =>
    cases restRun
    subst reserved
    let stack : StackLayout layout := {
      resultAddress:=address
      aligned:=aligned
      bounded:=bounded
      apartSmall:=apart _ _ (initialized_small layout)
      apartLarge:=apart _ _ (initialized_large layout) }
    have ownReserve : Owned (reserveLocal (initialDriver layout token world) "result" address uninitialized).heap :=
      allocateLocal_owned (initialized_owned layout) aligned bounded apart
    have bufferReserve : QuotientCInit.Buffers
        (reserveLocal (initialDriver layout token world) "result" address uninitialized).heap
        layout.smallBase layout.largeBase input.sqrt := reserved_buffers stack uninitialized
    have result := counter_call_exact
      (by simp [reserveLocal,initialDriver,globalEnv,QuotientCMachine.bind,emptyEnv])
      (by simp [reserveLocal,initialDriver,globalEnv,QuotientCMachine.bind,emptyEnv])
      ownReserve bufferReserve expression
    have rawEq : raw=.u64 (Nat.primeCounting input) := DriverValue.core.inj result.1
    subst raw
    have valueEq : value=Nat.primeCounting input := by
      rw [uint64_of_u64 actual_count_word_bound] at converted
      exact (Value.u64.inj (Option.some.inj converted)).symm
    subst value
    subst after
    refine ⟨by simp [initializeReserved],⟨address,?_,?_⟩,?_,?_⟩
    · simp [location,initializeReserved,result.2.2.1,reserveLocal]
    · exact stored_word_read actualStore
    · simp [initializeReserved,result.2.1,reserveLocal,initialDriver]
    · exact result.2.2.2.1

#print axioms declaration_result
end RamanujanPV.QuotientDriverSuccess
