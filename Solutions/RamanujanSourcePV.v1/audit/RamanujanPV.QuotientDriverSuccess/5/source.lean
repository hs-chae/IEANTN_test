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
      have read := read_of_block
        (heap:=Function.update heap address (some {block with words:=Function.update block.words index word}))
        (block:={block with words:=Function.update block.words index word})
        (by simp) good.1 good.2.1 good.2.2.1 (by simpa using good.2.2.2)
      simpa using read
    · contradiction

lemma counter_call_exact {layout : Layout} {token : Nat} {s t : DriverState} {value : DriverValue}
    (small : s.env "rpc_small"=some (.core (.ptr layout.smallBase)))
    (large : s.env "rpc_large"=some (.core (.ptr layout.largeBase)))
    (owned : Owned s.heap) (buffers : QuotientCInit.Buffers s.heap layout.smallBase layout.largeBase input.sqrt)
    (run : DriverEval token counterCall s t value) :
    value=.core (.u64 (Nat.primeCounting input)) ∧ t.env=s.env ∧ t.locations=s.locations ∧
      t.world=s.world ∧ Owned t.heap := by
  generalize he : counterCall=expression at run
  cases run with
  | pure evaluated =>
    rw [←he] at evaluated
    rw [counterCall,no_pure_call] at evaluated
    contradiction
  | address found typed storage => cases he
  | @internal name expressions before arguments values raw after heap value evaluated converted called post =>
    have hshape := Expr.call.inj he
    have hname := Expr.var.inj hshape.1
    cases hname
    cases hshape.2
    obtain ⟨rfl,rfl⟩ := counter_arguments_exact small large evaluated
    have rawEq : raw=([.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] : List Value) :=
      (Option.some.inj converted).symm
    subst raw
    rw [post]
    have result := driver_call_correct_of_buffers layout owned buffers called
    exact ⟨congrArg DriverValue.core result.1,rfl,rfl,rfl,result.2.1⟩
  | fwrite evaluated actual sizeCast countCast effect post =>
    have bad := Expr.var.inj (Expr.call.inj he).1
    exact ((by decide : "rpc_quotient_count" ≠ "fwrite") bad).elim
  | fflush evaluated actual effect post =>
    have bad := Expr.var.inj (Expr.call.inj he).1
    exact ((by decide : "rpc_quotient_count" ≠ "fflush") bad).elim
  | ne lhs rhs compared => cases he

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
    rw [initialized]
    refine ⟨by simp [initializeReserved],⟨address,?_,?_⟩,?_,?_⟩
    · simp [location,initializeReserved,result.2.2.1,reserveLocal]
    · exact stored_word_read actualStore
    · simp [initializeReserved,result.2.1,reserveLocal,initialDriver]
    · exact result.2.2.2.1

lemma no_pure_ne (heap : Heap) (env : Env) (left right : Expr) :
    evalPure QuotientSqrtExecute.noCalls heap env 8 (.binary "!=" left right)=none := by
  rw [pure_binary]
  cases ha : evalPure QuotientSqrtExecute.noCalls heap env 7 left with
  | none => rfl
  | some a =>
    cases hb : evalPure QuotientSqrtExecute.noCalls heap env 7 right with
    | none => rfl
    | some b => cases a <;> cases b <;> rfl

lemma eval_address_exact {token address : Nat} {s t : DriverState} {value : DriverValue}
    (found : location s "result"=some address)
    (run : DriverEval token (.unary "&" (.var "result")) s t value) :
    t=s ∧ value=.core (.ptr address) := by
  cases run with
  | pure evaluated => contradiction
  | address found' typed storage =>
    have eq := Option.some.inj (found.symm.trans found')
    cases eq
    exact ⟨rfl,rfl⟩

lemma write_arguments_exact {token address : Nat} {s t : DriverState} {values : List DriverValue}
    (found : location s "result"=some address)
    (stdout : s.env "stdout"=some (.core (.ptr token)))
    (run : DriverArgs token [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"] s t values) :
    t=s ∧ values=[.core (.ptr address),.core (.i32 8),.core (.i32 1),.core (.ptr token)] := by
  cases run with
  | cons first rest =>
    obtain ⟨rfl,rfl⟩ := eval_address_exact found first
    cases rest with
    | cons second rest =>
      obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact second
      have hv : raw=.i32 8 := (Option.some.inj ((by norm_num [literal] : literal 8=some (.i32 8)).symm.trans hraw)).symm
      subst raw
      cases rest with
      | cons third rest =>
        obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact third
        have hv : raw=.i32 1 := (Option.some.inj (QuotientCInit.literal_one.symm.trans hraw)).symm
        subst raw
        cases rest with
        | cons fourth rest =>
          obtain ⟨rfl,rfl⟩ := eval_variable_exact stdout fourth
          cases rest
          exact ⟨rfl,rfl⟩

def writeCall : Expr := .call (.var "fwrite")
  [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"]
def flushCall : Expr := .call (.var "fflush") [.var "stdout"]
def writeTest : Expr := .binary "!=" writeCall (.nat 1)
def flushTest : Expr := .binary "!=" flushCall (.nat 0)
def writeBranch : Stmt := .branch writeTest (.returnStmt (.nat 1)) .skip
def flushBranch : Stmt := .branch flushTest (.returnStmt (.nat 1)) .skip

lemma write_call_effect {token address : Nat} {s t : DriverState} {value : DriverValue}
    (found : location s "result"=some address)
    (stdout : s.env "stdout"=some (.core (.ptr token)))
    (run : DriverEval token writeCall s t value) :
    ∃ code world, t={s with world:=world} ∧ value=.core (.u64 code) ∧
      Fwrite s.heap address s.world world code := by
  generalize he : writeCall=expression at run
  cases run with
  | pure evaluated => rw [←he,writeCall,no_pure_call] at evaluated; contradiction
  | address found' typed storage => cases he
  | internal evaluated converted called post =>
    have shape := Expr.call.inj he
    have name := Expr.var.inj shape.1
    cases name
    cases called with
    | execute lookup arguments body =>
      change none=some _ at lookup
      contradiction
  | @fwrite expressions before arguments values writeAddress size count after returned world evaluated actual sizeCast countCast effect post =>
    have shape := Expr.call.inj he
    cases shape.2
    obtain ⟨rfl,rfl⟩ := write_arguments_exact found stdout evaluated
    cases actual
    exact ⟨returned,world,post,rfl,effect⟩
  | fflush evaluated actual effect post =>
    have bad := Expr.var.inj (Expr.call.inj he).1
    exact ((by decide : "fwrite" ≠ "fflush") bad).elim
  | ne lhs rhs compared => cases he

lemma flush_call_effect {token : Nat} {s t : DriverState} {value : DriverValue}
    (stdout : s.env "stdout"=some (.core (.ptr token)))
    (run : DriverEval token flushCall s t value) :
    ∃ code world, t={s with world:=world} ∧ value=.signed code ∧ Fflush s.world world code := by
  generalize he : flushCall=expression at run
  cases run with
  | pure evaluated => rw [←he,flushCall,no_pure_call] at evaluated; contradiction
  | address found typed storage => cases he
  | internal evaluated converted called post =>
    have shape := Expr.call.inj he
    have name := Expr.var.inj shape.1
    cases name
    cases called with
    | execute lookup arguments body => change none=some _ at lookup; contradiction
  | fwrite evaluated actual sizeCast countCast effect post =>
    have bad := Expr.var.inj (Expr.call.inj he).1
    exact ((by decide : "fflush" ≠ "fwrite") bad).elim
  | @fflush expressions before arguments values after returned world evaluated actual effect post =>
    have shape := Expr.call.inj he
    cases shape.2
    cases evaluated with
    | cons first rest =>
      obtain ⟨rfl,rfl⟩ := eval_variable_exact stdout first
      cases rest
      exact ⟨returned,world,post,rfl,effect⟩
  | ne lhs rhs compared => cases he

lemma write_test_success {token : Nat} {world : World} {s t : DriverState} {value : DriverValue}
    (rep : ResultRep token world s) (run : DriverEval token writeTest s t value)
    (success : driverTruth value=false) :
    t.env=s.env ∧ t.locations=s.locations ∧ t.heap=s.heap ∧
      t.world.buffered=s.world.buffered++wordBytes (Nat.primeCounting input) ∧
      t.world.committed=s.world.committed := by
  change DriverEval token (.binary "!=" writeCall (.nat 1)) s t value at run
  cases run with
  | pure evaluated => rw [no_pure_ne] at evaluated; contradiction
  | ne lhs rhs compared =>
    obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact rhs
    have hv : raw=.i32 1 := (Option.some.inj (QuotientCInit.literal_one.symm.trans hraw)).symm
    subst raw
    obtain ⟨address,found,read⟩ := rep.address
    obtain ⟨code,next,post,rfl,effect⟩ := write_call_effect found rep.stdout lhs
    cases effect with
    | complete other =>
      have eq : value=.core (.i32 0) := (Option.some.inj (notEqual_write_success.symm.trans compared)).symm
      have results := successful_fwrite (before:=s.world) read (Fwrite.complete (before:=s.world) other)
      rw [post]
      exact ⟨rfl,rfl,rfl,results.1,results.2⟩
    | failed =>
      have failedComparison : notEqual (.core (.u64 0)) (.core (.i32 1))=some (.core (.i32 1)) := by
        norm_num [notEqual,DriverValue.integer,DriverValue.unsigned,modulus]
      have eq : value=.core (.i32 1) := (Option.some.inj (failedComparison.symm.trans compared)).symm
      rw [eq] at success
      contradiction

lemma flush_test_success {token : Nat} {s t : DriverState} {value : DriverValue}
    (stdout : s.env "stdout"=some (.core (.ptr token)))
    (run : DriverEval token flushTest s t value) (success : driverTruth value=false) :
    t.env=s.env ∧ t.locations=s.locations ∧ t.heap=s.heap ∧
      t.world.buffered=[] ∧ t.world.committed=s.world.committed++s.world.buffered := by
  change DriverEval token (.binary "!=" flushCall (.nat 0)) s t value at run
  cases run with
  | pure evaluated => rw [no_pure_ne] at evaluated; contradiction
  | ne lhs rhs compared =>
    obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact rhs
    have hv : raw=.i32 0 := (Option.some.inj ((by norm_num [literal] : literal 0=some (.i32 0)).symm.trans hraw)).symm
    subst raw
    obtain ⟨code,next,post,rfl,effect⟩ := flush_call_effect stdout lhs
    cases effect with
    | complete =>
      rw [post]
      exact ⟨rfl,rfl,rfl,rfl,rfl⟩
    | failed after code nonzero =>
      have failedComparison : notEqual (.signed code) (.core (.i32 0))=some (.core (.i32 1)) := by
        simp [notEqual,DriverValue.integer,DriverValue.unsigned,nonzero]
      have eq : value=.core (.i32 1) := (Option.some.inj (failedComparison.symm.trans compared)).symm
      rw [eq] at success
      contradiction

#print axioms write_test_success
#print axioms flush_test_success
#print axioms declaration_result
end RamanujanPV.QuotientDriverSuccess
