import HighDriverSource
import RamanujanPV.QuotientDriverSuccess
/-! Application-specific high-input proofs reusing the unchanged old generic
DriverRun/InternalCall/stdio semantics. No numerical result or successful I/O
is assumed. The initial representation is constructed from the actual globals. -/
namespace RHOcticPush.HighDriverRuntime
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open RamanujanPV RamanujanPV.QuotientCMachine
open RamanujanPV.QuotientDriverInit RamanujanPV.QuotientDriverExecution
open RamanujanPV.QuotientDriverSuccess
set_option autoImplicit false
set_option maxHeartbeats 4000000

def input : Nat := 1490000000000
def capacity : Nat := 1500000
abbrev counterCall := RHOcticPush.HighDriverSource.counterCall
abbrev program := RHOcticPush.HighDriverSource.program

theorem source_static_initialization (layout : Layout) :
    StaticInit program.globals [layout.smallBase, layout.largeBase]
      emptyHeap (initializedHeap layout) :=
  RamanujanPV.QuotientDriverInit.source_static_initialization layout

theorem source_call_domain :
    2 ≤ input ∧ input ≤ 2000000000000 ∧ Nat.sqrt input < capacity ∧
      input < modulus ∧ capacity < modulus := by
  norm_num [input, capacity, RamanujanPV.QuotientDriverSource.capacity, modulus, Nat.sqrt_lt]

theorem driver_arguments (layout : Layout) :
    parameters QuotientCSourceV2.countFunction.parameters
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] emptyEnv =
      some (QuotientCFunctionPrefix.input input capacity layout.smallBase layout.largeBase
        (initializedHeap layout)).env := by
  have hp := source_pointer_values_valid layout
  simp [parameters,argument,RHOcticPush.HighDriverSource.input,QuotientCSourceV2.countFunction,emptyEnv,uint64,Value.scalar,
    input,capacity,modulus,ValidValue] at hp ⊢
  simp [QuotientCFunctionPrefix.input,hp.1,hp.2]

theorem driver_call_correct_of_buffers (layout : Layout) {before after : Heap} {value : Value}
    (owned : Owned before)
    (buffers : QuotientCInit.Buffers before layout.smallBase layout.largeBase input.sqrt)
    (call : InternalCall registry QuotientSqrtExecute.service "rpc_quotient_count"
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] before after value) :
    value = .u64 (Nat.primeCounting input) ∧ Owned after ∧ SameShape before after := by
  cases call with
  | execute lookup arguments body =>
      have hc : registry "rpc_quotient_count" = some QuotientCSourceV2.countFunction := rfl
      rw [hc] at lookup
      have hf := Option.some.inj lookup
      subst_vars
      have he : parameters QuotientCSourceV2.countFunction.parameters
          [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase] emptyEnv =
          some (QuotientCFunctionPrefix.input input capacity layout.smallBase layout.largeBase before).env :=
        driver_arguments layout
      rw [he] at arguments
      have henv := Option.some.inj arguments
      subst_vars
      have result := QuotientCFunction.completed_execution_correct
        source_call_domain.1 source_call_domain.2.1 source_call_domain.2.2.1
        source_call_domain.2.2.2.2 owned buffers body
      exact ⟨result.1,result.2.2,QuotientCHeapShape.run_shape body⟩

/-- Byte sequence of one uint64 object under the explicitly selected 8-bit,
little-endian ABI. This is an ABI choice, not a mathematical count premise. -/

theorem reserved_buffers {layout : Layout} (stack : StackLayout layout) (word : Nat) :
    QuotientCInit.Buffers (allocateLocal (initializedHeap layout) stack.resultAddress word)
      layout.smallBase layout.largeBase input.sqrt := by
  refine ⟨layout.distinct,zeroBlock smallArray,zeroBlock largeArray,?_,?_,
    source_call_domain.2.2.1,source_call_domain.2.2.1⟩
  · simp [allocateLocal,Function.update_of_ne stack.distinct_small.symm,initialized_small]
  · simp [allocateLocal,Function.update_of_ne stack.distinct_large.symm,initialized_large]

theorem actual_count_word_bound : Nat.primeCounting input < modulus := by
  have hsq : input < (input+1)*(input+1) := by have h := source_call_domain.1; nlinarith
  have htotal := QuotientSieve.total_final hsq
  have hle := QuotientWordBounds.total_le_argument (input+1) input
  rw [htotal] at hle
  exact hle.trans_lt source_call_domain.2.2.2.1

lemma initial_counter_arguments (layout : Layout) (stack : StackLayout layout) (token : Nat) (world : World) :
    DriverArgs token [.nat input,.nat capacity,.var "rpc_small",.var "rpc_large"]
      (reserveLocal (initialDriver layout token world) "result" stack.resultAddress 0)
      (reserveLocal (initialDriver layout token world) "result" stack.resultAddress 0)
      [.core (.i64 input),.core (.i32 capacity),.core (.ptr layout.smallBase),.core (.ptr layout.largeBase)] := by
  apply DriverArgs.cons (driver_literal _ _ _ (by norm_num [literal,input,RHOcticPush.HighDriverSource.input,RHOcticPush.HighDriverSource.input]))
  apply DriverArgs.cons (driver_literal _ _ _ (by norm_num [literal,capacity]))
  apply DriverArgs.cons (driver_variable _ _ _ (by simp [reserveLocal,initialDriver,globalEnv,QuotientCMachine.bind,emptyEnv]))
  apply DriverArgs.cons (driver_variable _ _ _ (by simp [reserveLocal,initialDriver,globalEnv,QuotientCMachine.bind,emptyEnv]))
  exact DriverArgs.nil _

/-- A complete source-AST success execution is constructible from the proved
actual callee execution and the generic stdio success rules. This is a logical
execution, not an assertion that a physical fflush succeeds. The separate
universal-success theorem must also exclude all failure-return alternatives. -/

theorem possible_success_source_run (layout : Layout) (stack : StackLayout layout)
    (token : Nat) (world : World) :
    ∃ final, DriverRun token program.main.body (initialDriver layout token world)
        (.returned final (.core (.i32 0))) ∧ final.world.buffered = [] ∧
      final.world.committed = world.committed ++ world.buffered ++ wordBytes (Nat.primeCounting input) := by
  let start := initialDriver layout token world
  let reserved := reserveLocal start "result" stack.resultAddress 0
  let pc := Nat.primeCounting input
  have ownedReserved : Owned reserved.heap :=
    allocateLocal_owned (initialized_owned layout) stack.aligned stack.bounded stack.apart
  have buffersReserved : QuotientCInit.Buffers reserved.heap layout.smallBase layout.largeBase input.sqrt :=
    reserved_buffers stack 0
  obtain ⟨callee,linked,calleeEnv,calleeOwned⟩ := QuotientCFunction.linked_function_refines input capacity
    layout.smallBase layout.largeBase reserved.heap source_call_domain.1 source_call_domain.2.1
    source_call_domain.2.2.1 source_call_domain.2.2.2.2 ownedReserved buffersReserved
  have internal : InternalCall registry QuotientSqrtExecute.service "rpc_quotient_count"
      [.i64 input,.i32 capacity,.ptr layout.smallBase,.ptr layout.largeBase]
      reserved.heap callee.heap (.u64 pc) :=
    InternalCall.execute (by rfl) (driver_arguments layout) linked.1
  let returned : DriverState := {reserved with heap := callee.heap}
  have callExpr : DriverEval token counterCall reserved returned (.core (.u64 pc)) :=
    DriverEval.internal (initial_counter_arguments layout stack token world) rfl internal rfl
  have shape : SameShape reserved.heap callee.heap := QuotientCHeapShape.run_shape linked.1
  obtain ⟨cell,hcell,hextent⟩ := QuotientCHeapShape.extent_preserved shape
    (base := stack.resultAddress) (block := localWord 0)
    (by simp [reserved,reserveLocal,allocateLocal])
  let written : Heap := Function.update callee.heap stack.resultAddress
    (some {cell with words := Function.update cell.words 0 pc})
  have store : write returned.heap stack.resultAddress 0 pc = some written :=
    write_of_block hcell stack.aligned (by simp [hextent,localWord])
      (by simpa using stack.bounded) actual_count_word_bound
  let initialized := initializeReserved returned "result" pc written
  have resultEnv : initialized.env "result" = some (.core (.u64 pc)) := by
    simp [initialized,initializeReserved]
  have resultLocation : location initialized "result" = some stack.resultAddress := by
    simp [location,initialized,initializeReserved,returned,reserved,reserveLocal]
  have resultRead : QuotientCMachine.read initialized.heap stack.resultAddress 0 = some (.u64 pc) := by
    have h := read_of_block (heap := written) (base := stack.resultAddress) (index := 0)
      (block := {cell with words := Function.update cell.words 0 pc})
      (by simp [written]) stack.aligned (by change 0 < cell.extent; simp [hextent,localWord])
      (by simpa using stack.bounded) (by simpa using actual_count_word_bound)
    simpa [initialized,initializeReserved] using h
  have declaration : DriverDeclare token [⟨"uint64_t","result",some counterCall⟩] start initialized := by
    apply DriverDeclare.cons (uninitialized := 0) (reserved := reserved) (middle := returned)
      (address := stack.resultAddress) (written := written)
    · norm_num [modulus]
    · simp [start,initialDriver,globalEnv,QuotientCMachine.bind,emptyEnv]
    · rfl
    · exact stack.fresh
    · exact stack.aligned
    · exact stack.bounded
    · exact stack.apart
    · rfl
    · exact callExpr
    · exact uint64_of_u64 actual_count_word_bound
    · exact actual_count_word_bound
    · exact store
    · rfl
    · exact DriverDeclare.nil _
  have stdoutInitialized : initialized.env "stdout" = some (.core (.ptr token)) := by
    simp [initialized,initializeReserved,returned,reserved,reserveLocal,start,initialDriver]
  have writeArgs : DriverArgs token [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"]
      initialized initialized
      [.core (.ptr stack.resultAddress),.core (.i32 8),.core (.i32 1),.core (.ptr token)] :=
    DriverArgs.cons (DriverEval.address resultLocation resultEnv resultRead)
      (DriverArgs.cons (driver_literal _ _ _ (by norm_num [literal]))
      (DriverArgs.cons (driver_literal _ _ _ QuotientCInit.literal_one)
      (DriverArgs.cons (driver_variable _ _ _ stdoutInitialized) (DriverArgs.nil _))))
  let writtenWorld : World := ⟨world.buffered ++ wordBytes pc,world.committed⟩
  let wrote : DriverState := {initialized with world := writtenWorld}
  have fwriteExpr : DriverEval token
      (.call (.var "fwrite") [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"])
      initialized wrote (.core (.u64 1)) := by
    apply DriverEval.fwrite writeArgs rfl
    · norm_num [uint64,Value.scalar,modulus]
    · norm_num [uint64,Value.scalar,modulus]
    · exact Fwrite.complete resultRead
    · rfl
  have writeTest : DriverEval token (.binary "!="
      (.call (.var "fwrite") [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"]) (.nat 1))
      initialized wrote (.core (.i32 0)) :=
    DriverEval.ne fwriteExpr (driver_literal _ _ _ QuotientCInit.literal_one) notEqual_write_success
  have writeBranch : DriverRun token (.branch (.binary "!="
      (.call (.var "fwrite") [.unary "&" (.var "result"),.nat 8,.nat 1,.var "stdout"]) (.nat 1))
      (.returnStmt (.nat 1)) .skip) initialized (.continuing wrote) := by
    apply StmtRun.branch writeTest
    simpa [driverTruth,DriverValue.integer] using StmtRun.skip
      (Eval := DriverEval token) (Declare := DriverDeclare token)
      (truth := driverTruth) (Scope := DriverScope) wrote
  have stdoutWrote : wrote.env "stdout" = some (.core (.ptr token)) := stdoutInitialized
  have flushArgs : DriverArgs token [.var "stdout"] wrote wrote [.core (.ptr token)] :=
    DriverArgs.cons (driver_variable _ _ _ stdoutWrote) (DriverArgs.nil _)
  let flushedWorld : World := ⟨[],world.committed ++ (world.buffered ++ wordBytes pc)⟩
  let flushed : DriverState := {wrote with world := flushedWorld}
  have fflushExpr : DriverEval token (.call (.var "fflush") [.var "stdout"])
      wrote flushed (.signed 0) :=
    DriverEval.fflush flushArgs rfl (Fflush.complete writtenWorld) rfl
  have flushTest : DriverEval token
      (.binary "!=" (.call (.var "fflush") [.var "stdout"]) (.nat 0))
      wrote flushed (.core (.i32 0)) :=
    DriverEval.ne fflushExpr (driver_literal _ _ _ (by norm_num [literal])) notEqual_flush_success
  have flushBranch : DriverRun token (.branch
      (.binary "!=" (.call (.var "fflush") [.var "stdout"]) (.nat 0))
      (.returnStmt (.nat 1)) .skip) wrote (.continuing flushed) := by
    apply StmtRun.branch flushTest
    simpa [driverTruth,DriverValue.integer] using StmtRun.skip
      (Eval := DriverEval token) (Declare := DriverDeclare token)
      (truth := driverTruth) (Scope := DriverScope) flushed
  let final := closeDriverScope start flushed
  refine ⟨final,?_,rfl,?_⟩
  · apply StmtRun.sequence (inner := .returned flushed (.core (.i32 0)))
    · exact SeqRun.next (StmtRun.declare declaration)
        (SeqRun.next writeBranch (SeqRun.next flushBranch
        (SeqRun.returned (StmtRun.returnValue (driver_literal _ _ _ (by norm_num [literal]))))))
    · rfl
  · simp [final,closeDriverScope,flushed,flushedWorld,pc,List.append_assoc]

lemma counter_arguments_exact {layout : Layout} {token : Nat} {s t : DriverState} {values : List DriverValue}
    (small : s.env "rpc_small"=some (.core (.ptr layout.smallBase)))
    (large : s.env "rpc_large"=some (.core (.ptr layout.largeBase)))
    (run : DriverArgs token [.nat input,.nat capacity,.var "rpc_small",.var "rpc_large"] s t values) :
    t=s ∧ values=[.core (.i64 input),.core (.i32 capacity),.core (.ptr layout.smallBase),.core (.ptr layout.largeBase)] := by
  cases run with
  | cons first rest =>
    obtain ⟨raw,hraw,rfl,rfl⟩ := eval_nat_exact first
    have hv : raw=.i64 input := by simpa [literal,input,RHOcticPush.HighDriverSource.input,RHOcticPush.HighDriverSource.input] using (Option.some.inj ((by norm_num [literal,input,RHOcticPush.HighDriverSource.input,RHOcticPush.HighDriverSource.input] : literal input=some (.i64 input)).symm.trans hraw)).symm
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
    rw [counterCall,RHOcticPush.HighDriverSource.counterCall,no_pure_call] at evaluated
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

lemma main_source_shape : program.main.body=.sequence [
    .declare [⟨"uint64_t","result",some counterCall⟩],writeBranch,flushBranch,.returnStmt (.nat 0)] := rfl

/-- EVERY successful modeled execution of the entire actual main function
commits precisely the bytes of the actual prime count. Failure branches, partial
writes and negative flush errors are retained in the semantics and excluded by
its actual source return0. No successful-stdio effect is assumed as a premise. -/

theorem successful_main_output (layout : Layout) (token : Nat) (world : World)
    {final : DriverState}
    (run : DriverRun token program.main.body (initialDriver layout token world)
      (.returned final (.core (.i32 0)))) :
    final.world.buffered=[] ∧
      final.world.committed=world.committed++world.buffered++wordBytes (Nat.primeCounting input) := by
  rw [main_source_shape] at run
  obtain ⟨inner,sequence,scope⟩ := sequence_returned run
  rw [scope]
  change inner.world.buffered=[] ∧ inner.world.committed=_
  cases sequence with
  | returned first => cases first
  | next first rest =>
    cases first with
    | declare declaration =>
      have rep := declaration_result declaration
      cases rest with
      | returned first => exact (branch_cannot_return_zero first).elim
      | next writeRun rest =>
        obtain ⟨middle,value,test,stop,rfl⟩ := branch_continuing writeRun
        have wrote := write_test_success rep test stop
        cases rest with
        | returned first => exact (branch_cannot_return_zero first).elim
        | next flushRun rest =>
          obtain ⟨middle,value,test,stop,rfl⟩ := branch_continuing flushRun
          have stdout : _ := rep.stdout
          have flushed := flush_test_success (by rw [wrote.1]; exact stdout) test stop
          cases rest with
          | next first rest => cases first
          | returned first =>
            cases first with
            | returnValue evaluated =>
              obtain ⟨raw,hraw,rfl,hvalue⟩ := eval_nat_exact evaluated
              refine ⟨flushed.2.2.2.1,?_⟩
              rw [flushed.2.2.2.2,wrote.2.2.2.2,wrote.2.2.2.1,rep.sameWorld]
              simp [List.append_assoc]

#print axioms source_static_initialization
#print axioms source_call_domain
#print axioms driver_call_correct_of_buffers
#print axioms possible_success_source_run
#print axioms successful_main_output
end RHOcticPush.HighDriverRuntime
