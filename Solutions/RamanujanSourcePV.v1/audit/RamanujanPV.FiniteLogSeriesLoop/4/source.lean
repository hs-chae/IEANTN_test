/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteLogServices
import RamanujanPV.FiniteLogNormalize
import RamanujanPV.FiniteLogBounds
import RamanujanPV.FiniteCellWords

/-! Actual twenty-iteration C loop for the original ceil-rounded logarithm
series. Every modular ceil response is source-realized by FiniteLogServices. -/
namespace RamanujanPV.FiniteLogSeriesLoop
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules AnalyticTransition
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

abbrev F : Nat := 2^60
abbrev P := FiniteLogCeil.prototypes
abbrev C := FiniteLogServices.ceilService

def sumPrefix (z z2 k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, sourceCeilDiv (log20Power F z z2 i) (2*i+1)

lemma prefix_zero (z z2 : Nat) : sumPrefix z z2 0=0 := by simp [sumPrefix]
lemma prefix_succ (z z2 k : Nat) :
    sumPrefix z z2 (k+1)=sumPrefix z z2 k+sourceCeilDiv (log20Power F z z2 k) (2*k+1) := by
  simp [sumPrefix,Finset.sum_range_succ]
lemma prefix_twenty (z z2 : Nat) : sumPrefix z z2 20=log20Sum F z z2 := rfl

structure Reads (s : State) (z z2 k : Nat) : Prop where
  read_F : s.env "F"=some (word64 F)
  read_z : s.env "z"=some (word64 z)
  read_z2 : s.env "z2"=some (word64 z2)
  read_power : s.env "power"=some (word64 (log20Power F z z2 k))
  read_sum : s.env "sum"=some (word128 (sumPrefix z z2 k))
  read_k : s.env "k"=some (word64 k)

def Frame (s t : State) : Prop :=
  ∀ name, name≠"power" → name≠"sum" → name≠"k" → t.env name=s.env name

def condition : Expr := .binary "<" (.var "k") (.nat 20)
def step : Expr := .unary "++" (.var "k")
def termExpr : Expr := .call (.var "rpc_log_ceildiv") [
  .var "power",.binary "+" (.binary "*" (.nat 2) (.var "k")) (.nat 1)]
def powerExpr : Expr := .call (.var "rpc_log_ceildiv") [
  .binary "*" (.cast "__uint128_t" (.var "power")) (.var "z2"),.var "F"]
def body : Stmt := .sequence [
  .eval (.binary "=" (.var "sum") (.binary "+" (.var "sum") termExpr)),
  .eval (.binary "=" (.var "power") powerExpr)]
def sourceFor : Stmt := .forLoop (.declare [⟨"uint64_t","k",some (.nat 0)⟩])
  (some condition) step body

theorem actual_source_subtree :
    (match FiniteLogSource.seriesFunction.body with
      | .sequence statements => statements[5]?
      | _ => none)=some sourceFor := rfl

lemma prefix_bound {z z2 k : Nat} (hz : z≤2^59) (hz2 : z2≤2^59) (hk : k≤20) :
    sumPrefix z z2 k<2^128 := by
  have bound := FiniteLogBounds.prefix_sum_bound hz hz2 k
  change sumPrefix z z2 k≤k*F at bound
  have mul := Nat.mul_le_mul_right F hk
  norm_num [F] at bound mul ⊢
  omega

lemma power_word {z z2 : Nat} (hz : z≤2^59) (hz2 : z2≤2^59) (k : Nat) :
    log20Power F z z2 k<2^64 :=
  (FiniteLogBounds.power_bound hz hz2 k).trans_lt (by norm_num)

lemma cast64_128 {n : Nat} (hn : n<2^128) :
    WideScalar.cast u128 (word64 n)=some (word128 n) :=
  cast_number _ (by decide) (range_nat hn)
lemma cast128_same {n : Nat} (hn : n<2^128) :
    WideScalar.cast u128 (word128 n)=some (word128 n) :=
  cast_number _ (by decide) (range_nat hn)

/-- Opaque composition for an actual two-argument source call. -/
lemma pure_call_two {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name : String} {left right : Expr} {a b result : Value}
    (hl : pure p c env fuel left=some a) (hr : pure p c env fuel right=some b)
    (called : invoke p c name [a,b]=some result) :
    pure p c env (fuel+1) (.call (.var name) [left,right])=some result := by
  simp only [FiniteScalarMachine.pure,List.mapM_cons,List.mapM_nil,hl,hr,Option.bind,Option.pure_def]
  exact called

def sumState (s : State) (z z2 k : Nat) : State :=
  ⟨FiniteScalarMachine.bind s.env "sum" (word128 (sumPrefix z z2 (k+1)))⟩
def bodyState (s : State) (z z2 k : Nat) : State :=
  ⟨FiniteScalarMachine.bind (sumState s z z2 k).env "power" (word64 (log20Power F z z2 (k+1)))⟩
def nextState (s : State) (z z2 k : Nat) : State :=
  ⟨FiniteScalarMachine.bind (bodyState s z z2 k).env "k" (word64 (k+1))⟩

lemma next_reads {s : State} {z z2 k : Nat} (h : Reads s z z2 k) :
    Reads (nextState s z z2 k) z z2 (k+1) := by
  constructor <;>simp [nextState,bodyState,sumState,FiniteScalarMachine.bind,Function.update,
    h.read_F,h.read_z,h.read_z2,h.read_k]
lemma next_frame (s : State) (z z2 k : Nat) : Frame s (nextState s z z2 k) := by
  intro name np ns nk
  simp [nextState,bodyState,sumState,FiniteScalarMachine.bind,Function.update,np,ns,nk]

lemma left_two_mul {k : Nat} (hk : k≤20) :
    WideScalar.binary "*" (i32 2) (word64 k)=some (word64 (2*k)) := by
  have kb : k<2^64 := by norm_num at hk ⊢;omega
  have prod : 2*k<2^64 := by norm_num at hk ⊢;omega
  have h : Operands 64 (i32 2) (word64 k) :=
    ⟨by decide +kernel,FiniteLogNormalize.word_valid kb,rfl,by norm_num [Range,i32],range_nat kb⟩
  simpa [i32,word64,scalarWord,unsignedType,u64,Nat.cast_mul] using
    FiniteScalarRules.mul (by decide : 0<64) h
      (show Range 64 ((i32 2).number*(word64 k).number) by
        simpa [i32,word64,Nat.cast_mul] using range_nat prod)

lemma denominator_pure {s : State} {k : Nat} {fuel : Nat} (hk : k≤20)
    (read : s.env "k"=some (word64 k)) :
    pure P C s.env (fuel+3) (.binary "+" (.binary "*" (.nat 2) (.var "k")) (.nat 1))=
      some (word64 (2*k+1)) := by
  have mul : pure P C s.env (fuel+2) (.binary "*" (.nat 2) (.var "k"))=
      some (word64 (2*k)) :=
    FiniteScalarMachine.pure_binary (pure_literal (by decide +kernel))
      (pure_variable read) (left_two_mul hk)
  exact FiniteScalarMachine.pure_binary mul (pure_literal (by decide +kernel))
    (FiniteLogNormalize.word_add_one (by norm_num at hk ⊢;omega) (by norm_num at hk ⊢;omega))

lemma term_pure {s : State} {z z2 k : Nat} {fuel : Nat}
    (hz : z≤2^59) (hz2 : z2≤2^59) (hk : k≤20) (h : Reads s z z2 k) :
    pure P C s.env (fuel+4) termExpr=
      some (word64 (sourceCeilDiv (log20Power F z z2 k) (2*k+1))) := by
  have pb := power_word hz hz2 k
  have db : 2*k+1<2^128 := by norm_num at hk ⊢;omega
  have out : sourceCeilDiv (log20Power F z z2 k) (2*k+1)<2^64 :=
    (FiniteLogBounds.term_bound hz hz2 k).trans_lt (by norm_num)
  exact pure_call_two (pure_variable h.read_power) (denominator_pure hk h.read_k)
    (FiniteLogServices.invoke_ceil (cast64_128 (pb.trans (by norm_num)))
      (cast64_128 db) (pb.trans (by norm_num)) db (by omega) out)

lemma power_pure {s : State} {z z2 k : Nat} {fuel : Nat}
    (hz : z≤2^59) (hz2 : z2≤2^59) (hF : s.env "F"=some (word64 F))
    (hp : s.env "power"=some (word64 (log20Power F z z2 k)))
    (hr : s.env "z2"=some (word64 z2)) :
    pure P C s.env (fuel+4) powerExpr=some (word64 (log20Power F z z2 (k+1))) := by
  have pb := power_word hz hz2 k
  have zb : z2<2^64 := hz2.trans_lt (by norm_num)
  have product : log20Power F z z2 k*z2<2^128 := by
    have hp := FiniteLogBounds.power_bound hz hz2 k
    have mul := Nat.mul_le_mul hp hz2
    norm_num at mul ⊢
    omega
  have pw : pure P C s.env (fuel+2) (.cast "__uint128_t" (.var "power"))=
      some (word128 (log20Power F z z2 k)) :=
    pure_cast rfl (pure_variable hp) (cast64_128 (pb.trans (by norm_num)))
  have expr : pure P C s.env (fuel+3)
      (.binary "*" (.cast "__uint128_t" (.var "power")) (.var "z2"))=
      some (word128 (log20Power F z z2 k*z2)) :=
    FiniteScalarMachine.pure_binary pw (pure_variable hr)
      (FiniteCellWords.u128_mul64 (pb.trans (by norm_num)) zb product)
  change pure P C s.env (fuel+4) (.call (.var "rpc_log_ceildiv") [
    .binary "*" (.cast "__uint128_t" (.var "power")) (.var "z2"),.var "F"])=_
  exact pure_call_two expr (pure_variable hF)
    (FiniteLogServices.invoke_ceil (cast128_same product) (cast64_128 (by norm_num))
      product (by norm_num) (by norm_num) (power_word hz hz2 (k+1)))

lemma condition_eval {s : State} {z z2 k : Nat} (hk : k≤20) (h : Reads s z z2 k) :
    Eval P C condition s s (WideScalar.boolean (decide (k<20))) := by
  have kb : k<2^64 := by norm_num at hk ⊢;omega
  have eval : pure P C s.env 8 condition=some (WideScalar.boolean (decide (k<20))) :=
    FiniteScalarMachine.pure_binary (pure_variable h.read_k) (pure_literal (by decide +kernel))
      (FiniteCellWords.u64_signed_lt kb (w:=32) (Or.inl rfl) (by decide +kernel))
  change (do return (s,←pure P C s.env 8 condition))=some _
  rw [eval]
  rfl

lemma body_scope {s : State} {z z2 k : Nat} (h : Reads s z z2 k) :
    closeScope s (bodyState s z z2 k)=bodyState s z z2 k := by
  apply congrArg State.mk
  funext name
  by_cases np : name="power"
  · subst name
    simp [closeScope,bodyState,sumState,FiniteScalarMachine.bind,h.read_power]
  by_cases ns : name="sum"
  · subst name
    simp [closeScope,bodyState,sumState,FiniteScalarMachine.bind,h.read_sum]
  · change (if (s.env name).isSome then (bodyState s z z2 k).env name else none)=_
    have same : (bodyState s z z2 k).env name=s.env name := by
      simp [bodyState,sumState,FiniteScalarMachine.bind,Function.update,np,ns]
    rw [same]
    cases h : s.env name <;>simp [bodyState,sumState,FiniteScalarMachine.bind,Function.update,np,ns,h]

lemma body_exec {s : State} {z z2 k : Nat}
    (hz : z≤2^59) (hz2 : z2≤2^59) (hk : k<20) (h : Reads s z z2 k) :
    Run P C body s (.continuing (bodyState s z z2 k)) := by
  have sb := prefix_bound hz hz2 hk.le
  have nextb := prefix_bound hz hz2 (by omega : k+1≤20)
  have tb : sourceCeilDiv (log20Power F z z2 k) (2*k+1)<2^64 :=
    (FiniteLogBounds.term_bound hz hz2 k).trans_lt (by norm_num)
  have sumOp : WideScalar.binary "+" (word128 (sumPrefix z z2 k))
      (word64 (sourceCeilDiv (log20Power F z z2 k) (2*k+1)))=
      some (word128 (sumPrefix z z2 (k+1))) := by
    have eq := prefix_succ z z2 k
    have sumRange : Range 128 ((word128 (sumPrefix z z2 k)).number+
        (word64 (sourceCeilDiv (log20Power F z z2 k) (2*k+1))).number) := by
      simpa only [word64,word128,←Nat.cast_add,←eq] using range_nat nextb
    have op := FiniteScalarRules.add (by decide : 0<128)
      (FiniteCellWords.operands128_64 sb tb) sumRange
    simpa only [word64,word128,scalarWord,unsignedType,u128,←Nat.cast_add,←eq] using op
  have addition : pure P C s.env 8 (.binary "+" (.var "sum") termExpr)=
      some (word128 (sumPrefix z z2 (k+1))) :=
    FiniteScalarMachine.pure_binary (pure_variable h.read_sum)
      (term_pure (fuel:=3) hz hz2 hk.le h) sumOp
  have storeSum : Eval P C (.binary "=" (.var "sum") (.binary "+" (.var "sum") termExpr))
      s (sumState s z z2 k) (word128 (sumPrefix z z2 (k+1))) :=
    FiniteLogNormalize.eval_assign_of h.read_sum addition (cast128_same nextb)
  have sumF : (sumState s z z2 k).env "F"=some (word64 F) := by
    simpa [sumState,FiniteScalarMachine.bind,Function.update] using h.read_F
  have sumP : (sumState s z z2 k).env "power"=some (word64 (log20Power F z z2 k)) := by
    simpa [sumState,FiniteScalarMachine.bind,Function.update] using h.read_power
  have sumZ2 : (sumState s z z2 k).env "z2"=some (word64 z2) := by
    simpa [sumState,FiniteScalarMachine.bind,Function.update] using h.read_z2
  have power := power_pure (fuel:=4) hz hz2 sumF sumP sumZ2
  have storePower : Eval P C (.binary "=" (.var "power") powerExpr)
      (sumState s z z2 k) (bodyState s z z2 k) (word64 (log20Power F z z2 (k+1))) :=
    FiniteLogNormalize.eval_assign_of sumP power (FiniteLogNormalize.cast_word (power_word hz hz2 (k+1)))
  apply StmtRun.sequence
    (SeqRun.next (StmtRun.evaluate storeSum)
      (SeqRun.next (StmtRun.evaluate storePower) (SeqRun.nil (bodyState s z z2 k))))
  change Flow.continuing (bodyState s z z2 k)=Flow.continuing (closeScope s (bodyState s z z2 k))
  rw [body_scope h]

lemma increment_exec {s : State} {z z2 k : Nat} (hk : k<20) (h : Reads s z z2 k) :
    Eval P C step (bodyState s z z2 k) (nextState s z z2 k) (word64 (k+1)) := by
  have read : (bodyState s z z2 k).env "k"=some (word64 k) := by
    simpa [bodyState,sumState,FiniteScalarMachine.bind,Function.update] using h.read_k
  exact FiniteLogNormalize.eval_increment_of read
    (FiniteLogNormalize.word_add_one (by norm_num at hk ⊢;omega) (by norm_num at hk ⊢;omega))
    (FiniteLogNormalize.cast_word (by norm_num at hk ⊢;omega))

lemma loop_remaining (fuel : Nat) :
    ∀ (s : State) (z z2 k : Nat), z≤2^59 → z2≤2^59 → k+fuel=20 → Reads s z z2 k →
      ∃t,ForRun P C (some condition) step body s (.continuing t) ∧
        Reads t z z2 20 ∧ Frame s t := by
  induction fuel with
  | zero =>
    intro s z z2 k hz hz2 budget h
    have eq : k=20 := by omega
    subst k
    refine ⟨s,ForRun.done ?_,h,?_⟩
    · simpa only [WideScalar.truth,WideScalar.boolean,decide_false,↓reduceIte] using
        GuardRun.present (condition_eval (by omega : 20≤20) h)
    · intro name _ _ _;rfl
  | succ fuel ih =>
    intro s z z2 k hz hz2 budget h
    have hk : k<20 := by omega
    have tested := condition_eval hk.le h
    have guard : GuardRun (Eval P C) WideScalar.truth (some condition) s s true := by
      simpa only [WideScalar.truth,WideScalar.boolean,hk,decide_true,↓reduceIte] using
        GuardRun.present tested
    obtain ⟨t,rest,post,frame⟩ :=
      ih (nextState s z z2 k) z z2 (k+1) hz hz2 (by omega) (next_reads h)
    refine ⟨t,ForRun.next guard (body_exec hz hz2 hk h) (increment_exec hk h) rest,post,?_⟩
    intro name np ns nk
    exact (frame name np ns nk).trans (next_frame s z z2 k name np ns nk)

/-- The original source for-loop executes from any correctly represented prefix
and finishes at the original twenty-term power and sum. Its helper responses
are all realized by the actual rpc_log_ceildiv source body. -/
theorem loop_exec {s : State} {z z2 k : Nat}
    (hz : z≤2^59) (hz2 : z2≤2^59) (hk : k≤20) (h : Reads s z z2 k) :
    ∃t,ForRun P C (some condition) step body s (.continuing t) ∧
      Reads t z z2 20 ∧ Frame s t :=
  loop_remaining (20-k) s z z2 k hz hz2 (by omega) h

#print axioms actual_source_subtree
#print axioms prefix_bound
#print axioms pure_call_two
#print axioms next_reads
#print axioms term_pure
#print axioms power_pure
#print axioms body_exec
#print axioms increment_exec
#print axioms loop_exec
end RamanujanPV.FiniteLogSeriesLoop
