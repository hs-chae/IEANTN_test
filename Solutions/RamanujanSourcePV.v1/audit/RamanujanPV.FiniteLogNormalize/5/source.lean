/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteScalarRules
import RamanujanPV.FiniteLogSource
import RamanujanPV.FiniteLogNormalizationBounds

/-! Actual C execution of rpc_log_upper's normalization loop. Source syntax,
integer promotions, unsigned widths and scope effects are retained explicitly. -/
namespace RamanujanPV.FiniteLogNormalize
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def condition : Expr := .binary "<=" (.var "two") (.binary "/" (.var "n") (.nat 2))
def body : Stmt := .sequence [
  .eval (.binary "=" (.var "two") (.binary "*" (.var "two") (.nat 2))),
  .eval (.unary "++" (.var "k"))]
def normalization : Stmt := .whileLoop condition body

theorem actual_source_subtree :
    (match FiniteLogSource.upperFunction.body with
      | .sequence statements => statements[3]?
      | _ => none)=some normalization := rfl

lemma word_valid {n : Nat} (hn : n<2^64) :
    WideScalar.InRange (word64 n).type (word64 n).number :=
  scalar_range (by decide : 0<64) (range_nat hn)

lemma word_operands {a b : Nat} (ha : a<2^64) (hb : b<2^64) :
    Operands 64 (word64 a) (word64 b) :=
  ⟨word_valid ha,word_valid hb,rfl,range_nat ha,range_nat hb⟩

lemma two_operands {a : Nat} (ha : a<2^64) : Operands 64 (word64 a) (i32 2) :=
  ⟨word_valid ha,by decide +kernel,rfl,range_nat ha,by norm_num [Range,i32]⟩

lemma one_operands {a : Nat} (ha : a<2^64) : Operands 64 (word64 a) (i32 1) :=
  ⟨word_valid ha,by decide +kernel,rfl,range_nat ha,by norm_num [Range,i32]⟩

lemma word_div_two {a : Nat} (ha : a<2^64) :
    WideScalar.binary "/" (word64 a) (i32 2)=some (word64 (a/2)) := by
  have h:=FiniteScalarRules.div (by decide : 0<64) (two_operands ha) (by decide)
  have castDiv : (a:Int)/2=((a/2:Nat):Int) := by omega
  change WideScalar.binary "/" (word64 a) (i32 2)=some (scalarWord 64 ((a:Int)/2)) at h
  rw [castDiv] at h
  simpa [word64,scalarWord,unsignedType,u64] using h

lemma word_mul_two {a : Nat} (ha : a<2^64) (hnext : a*2<2^64) :
    WideScalar.binary "*" (word64 a) (i32 2)=some (word64 (a*2)) := by
  have range : Range 64 ((word64 a).number*(i32 2).number) := by
    constructor
    · simp only [word64,i32]; positivity
    · have bound : (a:Int)*2 < 2^64 := by exact_mod_cast hnext
      simpa only [word64,i32,Nat.cast_ofNat] using bound
  have h:=FiniteScalarRules.mul (by decide : 0<64) (two_operands ha) range
  simpa [word64,i32,scalarWord,unsignedType,u64,Nat.cast_mul] using h

lemma word_add_one {a : Nat} (ha : a<2^64) (hnext : a+1<2^64) :
    WideScalar.binary "+" (word64 a) (i32 1)=some (word64 (a+1)) := by
  have h:=FiniteScalarRules.add (by decide : 0<64) (one_operands ha)
    (show Range 64 ((word64 a).number+(i32 1).number) by
      simpa [word64,i32,Nat.cast_add] using range_nat hnext)
  simpa [word64,i32,scalarWord,unsignedType,u64,Nat.cast_add] using h

lemma word_le {a b : Nat} (ha : a<2^64) (hb : b<2^64) :
    WideScalar.binary "<=" (word64 a) (word64 b)=
      some (WideScalar.boolean (decide (a≤b))) := by
  simpa [word64] using FiniteScalarRules.le (by decide : 0<64) (word_operands ha hb)

lemma cast_word {n : Nat} (hn : n<2^64) :
    WideScalar.cast u64 (word64 n)=some (word64 n) := WideScalar.cast_same (word_valid hn)

lemma condition_pure {p : Prototypes} {c : Service} {s : State} {n two : Nat}
    (hn : s.env "n"=some (word64 n)) (ht : s.env "two"=some (word64 two))
    (nb : n<2^64) (tb : two<2^64) :
    pure p c s.env 8 condition=some (WideScalar.boolean (decide (two≤n/2))) := by
  have div : pure p c s.env 7 (.binary "/" (.var "n") (.nat 2))=some (word64 (n/2)) :=
    FiniteScalarMachine.pure_binary (pure_variable hn)
      (pure_literal (by decide +kernel : literal 2=some (i32 2))) (word_div_two nb)
  exact FiniteScalarMachine.pure_binary (pure_variable ht) div
    (word_le tb ((Nat.div_le_self n 2).trans_lt nb))

lemma condition_eval {p : Prototypes} {c : Service} {s : State} {n two : Nat}
    (hn : s.env "n"=some (word64 n)) (ht : s.env "two"=some (word64 two))
    (nb : n<2^64) (tb : two<2^64) :
    Eval p c condition s s (WideScalar.boolean (decide (two≤n/2))) := by
  change (do return (s,←pure p c s.env 8 condition))=some _
  rw [condition_pure hn ht nb tb]
  rfl

def middle (s : State) (two : Nat) : State :=
  ⟨FiniteScalarMachine.bind s.env "two" (word64 (two*2))⟩
def nextState (s : State) (two k : Nat) : State :=
  ⟨FiniteScalarMachine.bind (middle s two).env "k" (word64 (k+1))⟩

def Frame (s t : State) : Prop :=
  ∀ name, name≠"two" → name≠"k" → t.env name=s.env name

lemma next_reads {s : State} {n two k : Nat}
    (hn : s.env "n"=some (word64 n)) :
    (nextState s two k).env "n"=some (word64 n) ∧
    (nextState s two k).env "two"=some (word64 (two*2)) ∧
    (nextState s two k).env "k"=some (word64 (k+1)) := by
  simp [nextState,middle,FiniteScalarMachine.bind,Function.update,hn]

lemma next_frame (s : State) (two k : Nat) : Frame s (nextState s two k) := by
  intro name nt nk
  simp [nextState,middle,FiniteScalarMachine.bind,Function.update,nt,nk]

lemma next_scope {s : State} {two k : Nat}
    (ht : s.env "two"=some (word64 two)) (hk : s.env "k"=some (word64 k)) :
    closeScope s (nextState s two k)=nextState s two k := by
  apply congrArg State.mk
  funext name
  by_cases nt : name="two"
  · subst name
    simp [closeScope,nextState,middle,FiniteScalarMachine.bind,ht,hk]
  by_cases nk : name="k"
  · subst name
    simp [closeScope,nextState,middle,FiniteScalarMachine.bind,ht,hk]
  · have same := next_frame s two k name nt nk
    change (if (s.env name).isSome then (nextState s two k).env name else none)=_
    rw [same]
    cases h : s.env name <;>simp [nextState,middle,FiniteScalarMachine.bind,Function.update,nt,nk,h]

lemma body_exec {p : Prototypes} {c : Service} {s : State} {two k : Nat}
    (ht : s.env "two"=some (word64 two)) (hk : s.env "k"=some (word64 k))
    (tb : two<2^64) (kb : k<2^64)
    (tn : two*2<2^64) (kn : k+1<2^64) :
    Run p c body s (.continuing (nextState s two k)) := by
  have product : pure p c s.env 8 (.binary "*" (.var "two") (.nat 2))=some (word64 (two*2)) :=
    FiniteScalarMachine.pure_binary (pure_variable ht)
      (pure_literal (by decide +kernel : literal 2=some (i32 2))) (word_mul_two tb tn)
  have store : Eval p c (.binary "=" (.var "two") (.binary "*" (.var "two") (.nat 2)))
      s (middle s two) (word64 (two*2)) := by
    change (do
      let old ← s.env "two"
      let value ← pure p c s.env 8 (.binary "*" (.var "two") (.nat 2))
      let converted ← WideScalar.cast old.type value
      return (State.mk (FiniteScalarMachine.bind s.env "two" converted),converted))=some _
    rw [ht,product]
    change (do
      let converted ← WideScalar.cast u64 (word64 (two*2))
      return (State.mk (FiniteScalarMachine.bind s.env "two" converted),converted))=some _
    rw [cast_word tn]
    rfl
  have hm : (middle s two).env "k"=some (word64 k) := by
    simpa [middle,FiniteScalarMachine.bind,Function.update] using hk
  have increment : Eval p c (.unary "++" (.var "k"))
      (middle s two) (nextState s two k) (word64 (k+1)) := by
    change (do
      let old ← (middle s two).env "k"
      let value ← WideScalar.binary "+" old (i32 1)
      let converted ← WideScalar.cast old.type value
      return (State.mk (FiniteScalarMachine.bind (middle s two).env "k" converted),converted))=some _
    rw [hm]
    simp only [Option.bind]
    rw [word_add_one kb kn]
    change (do
      let converted ← WideScalar.cast u64 (word64 (k+1))
      return (State.mk (FiniteScalarMachine.bind (middle s two).env "k" converted),converted))=some _
    rw [cast_word kn]
    rfl
  apply StmtRun.sequence
    (SeqRun.next (StmtRun.evaluate store)
      (SeqRun.next (StmtRun.evaluate increment) (SeqRun.nil (nextState s two k))))
  change Flow.continuing (nextState s two k)=Flow.continuing (closeScope s (nextState s two k))
  rw [next_scope ht hk]

structure Normalized (s : State) (n two k : Nat) : Prop where
  read_n : s.env "n"=some (word64 n)
  read_two : s.env "two"=some (word64 two)
  read_k : s.env "k"=some (word64 k)
  power : two=2^k
  low : two≤n
  high : n<2*two
  bound : k≤40

lemma loop_remaining {p : Prototypes} {c : Service} (fuel : Nat) :
    ∀ (s : State) (n two k : Nat),
      s.env "n"=some (word64 n) → s.env "two"=some (word64 two) →
      s.env "k"=some (word64 k) → two=2^k → two≤n → n≤2000000000000 →
      k+fuel=41 → ∃ t finalTwo finalK,
        WhileRun p c condition body s (.continuing t) ∧
        Normalized t n finalTwo finalK ∧ Frame s t := by
  induction fuel with
  | zero =>
    intro s n two k hn ht hk hp low upper budget
    have bound := FiniteLogBounds.normalization_k_bound hp low upper
    omega
  | succ fuel ih =>
    intro s n two k hn ht hk hp low upper budget
    have bound := FiniteLogBounds.normalization_k_bound hp low upper
    have nb : n<2^64 := by norm_num at upper ⊢;omega
    have tb : two<2^64 := low.trans_lt nb
    have kb : k<2^64 := by norm_num at bound ⊢;omega
    have tested := condition_eval (p:=p) (c:=c) hn ht nb tb
    by_cases go : two≤n/2
    · obtain ⟨powNext,lowNext,kNext,tNext,kNextWord⟩ :=
        FiniteLogBounds.normalization_step hp upper go
      have reads := next_reads (two:=two) (k:=k) hn
      obtain ⟨t,finalTwo,finalK,rest,post,frame⟩ :=
        ih (nextState s two k) n (two*2) (k+1) reads.1 reads.2.1 reads.2.2
          powNext lowNext upper (by omega)
      refine ⟨t,finalTwo,finalK,
        WhileRun.next tested ?_ (body_exec ht hk tb kb tNext kNextWord) rest,post,?_⟩
      · simp [WideScalar.truth,WideScalar.boolean,go]
      · intro name nt nk
        exact (frame name nt nk).trans (next_frame s two k name nt nk)
    · have facts := FiniteLogBounds.normalization_stop hp low upper go
      refine ⟨s,two,k,WhileRun.done tested ?_,⟨hn,ht,hk,hp,low,facts.2.2.1,bound⟩,?_⟩
      · simp [WideScalar.truth,WideScalar.boolean,go]
      · intro name _ _;rfl

/-- The entire actual source loop terminates, produces the binary exponent and
retains every other binding. No logarithm value or expected output is assumed. -/
theorem normalization_exec {p : Prototypes} {c : Service} {s : State} {n two k : Nat}
    (hn : s.env "n"=some (word64 n)) (ht : s.env "two"=some (word64 two))
    (hk : s.env "k"=some (word64 k)) (power : two=2^k)
    (low : two≤n) (upper : n≤2000000000000) :
    ∃ t finalTwo finalK, Run p c normalization s (.continuing t) ∧
      Normalized t n finalTwo finalK ∧ Frame s t := by
  have bound := FiniteLogBounds.normalization_k_bound power low upper
  obtain ⟨t,finalTwo,finalK,loop,post,frame⟩ :=
    loop_remaining (41-k) s n two k hn ht hk power low upper (by omega)
  exact ⟨t,finalTwo,finalK,StmtRun.whileLoop loop,post,frame⟩

#print axioms body_exec
#print axioms normalization_exec
#print axioms actual_source_subtree
#print axioms condition_eval
end RamanujanPV.FiniteLogNormalize
