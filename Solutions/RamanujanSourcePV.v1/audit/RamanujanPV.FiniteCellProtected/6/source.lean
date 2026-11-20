/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellExecution
import RamanujanPV.FinitePredicateBounds
import RamanujanPV.FiniteScalarRules
import RamanujanPV.FiniteCellWords

/-! Protected-domain refinement of the ACTUAL thirteen-statement C row body.
The intended source precondition contains only non-strict guards and actual
helper responses. It never assumes the desired final strict inequality. -/
namespace RamanujanPV.FiniteCellProtected
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops FiniteScalarMachine
open WindowCells
set_option autoImplicit false
set_option maxHeartbeats 2000000

def reject (condition : Expr) : Stmt := .branch condition (.returnStmt (.nat 0)) .skip
def nGuard : Stmt := reject (.binary "<" (.var "n") (.nat 38358837683))
def advanceGuard : Stmt := reject (.binary "<=" (.var "next") (.var "n"))
def upperGuard : Stmt := reject (.binary ">" (.var "next") (.nat 2000000000001))
def jGuard : Stmt := reject (.binary ">" (.var "j") (.var "n"))
def qGuard : Stmt := reject (.binary ">" (.var "Q") (.var "j"))
def predecessor : Expr := .binary "-" (.var "next") (.nat 1)
def pGuard : Stmt := reject (.binary ">" (.var "P") predecessor)
def logPositiveGuard : Stmt := reject (.binary "==" (.var "Lu") (.nat 0))
def logGuard : Stmt := reject (.binary "!=" (.var "Lu") (.call (.var "rpc_log_upper") [.var "n"]))
def lowDeclaration : Stmt := .declare [⟨"uint64_t","lo",some (.call (.var "rpc_e_low") [])⟩]
def highDeclaration : Stmt := .declare [⟨"uint64_t","hi",some (.call (.var "rpc_e_high") [])⟩]
def jProduct : Expr := .binary "*" (.cast "__uint128_t" (.var "j")) (.var "hi")
def nProduct : Expr := .binary "*" (.cast "__uint128_t" (.var "n")) (.nat 1152921504606846976)
def quotient : Expr := .binary "/" (.binary "*" (.cast "__uint128_t" (.var "n")) (.var "lo")) (.var "Lu")
def jProductGuard : Stmt := reject (.binary ">" jProduct nProduct)
def aGuard : Stmt := reject (.binary "!=" (.cast "__uint128_t" (.var "A")) quotient)
def strictLeft : Expr := .binary "*"
  (.binary "*" (.cast "__uint128_t" (.nat 1048576)) (.var "P")) (.var "P")
def strictRight : Expr := .binary "*" (.cast "__uint128_t" (.var "A")) (.var "Q")
def strictExpr : Expr := .binary "<" strictLeft strictRight
def statements : List Stmt := [nGuard,advanceGuard,upperGuard,jGuard,qGuard,pGuard,
  logPositiveGuard,logGuard,lowDeclaration,highDeclaration,jProductGuard,aGuard,.returnStmt strictExpr]

theorem actual_body : FiniteCellSource.cellFunction.body=.sequence statements := rfl

structure Inputs (r : RawFactoredCell) (env : Env) : Prop where
  nValue : env "n"=some (word64 r.n)
  nextValue : env "next"=some (word64 r.next)
  jValue : env "j"=some (word64 r.j)
  pValue : env "P"=some (word64 r.P)
  qValue : env "Q"=some (word64 r.Q)
  luValue : env "Lu"=some (word64 r.Lu)
  aValue : env "A"=some (word64 r.A)

theorem input_fields (r : RawFactoredCell) : Inputs r (FiniteCellExecution.input r).env := by
  constructor <;> rfl

theorem Inputs.bind_other {r : RawFactoredCell} {env : Env} (h : Inputs r env)
    {name : String} (v : Value)
    (hn : name≠"n") (hnext : name≠"next") (hj : name≠"j")
    (hp : name≠"P") (hq : name≠"Q") (hlu : name≠"Lu") (ha : name≠"A") :
    Inputs r (FiniteScalarMachine.bind env name v) := by
  constructor
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hn)] using h.nValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hnext)] using h.nextValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hj)] using h.jValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hp)] using h.pValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hq)] using h.qValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm hlu)] using h.luValue
  · simpa [FiniteScalarMachine.bind,Function.update_of_ne (Ne.symm ha)] using h.aValue

structure WordFits (r : RawFactoredCell) : Prop where
  nWord : r.n < 2^64
  nextWord : r.next < 2^64
  jWord : r.j < 2^64
  pWord : r.P < 2^64
  qWord : r.Q < 2^64
  luWord : r.Lu < 2^64
  aWord : r.A < 2^64

/-- No final positivity clause. The call equation is an actual typed source
helper response, to be discharged by the completed source computations. -/
structure Domain (r : RawFactoredCell) extends WordFits r : Prop where
  nLower : 38358837683 ≤ r.n
  advance : r.n < r.next
  upper : r.next ≤ 2000000000001
  jBound : r.j ≤ r.n
  qBound : r.Q ≤ r.j
  pBound : r.P ≤ r.next-1
  logPositive : 0 < r.Lu
  logResponse : invoke FiniteCellExecution.prototypes FiniteCellExecution.service
    "rpc_log_upper" [word64 r.n]=some (word64 r.Lu)
  jExp : r.j*eHi ≤ r.n*2^60
  aFloor : r.A=(r.n*eLo)/r.Lu

def withLow (r : RawFactoredCell) : State :=
  ⟨FiniteScalarMachine.bind (FiniteCellExecution.input r).env "lo" (word64 eLo)⟩
def withBoth (r : RawFactoredCell) : State :=
  ⟨FiniteScalarMachine.bind (withLow r).env "hi" (word64 eHi)⟩

theorem low_fields (r : RawFactoredCell) : Inputs r (withLow r).env :=
  (input_fields r).bind_other _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem both_fields (r : RawFactoredCell) : Inputs r (withBoth r).env :=
  (low_fields r).bind_other _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem scope_two (s : State) (a b : Value)
    (hlo : s.env "lo"=none) (hhi : s.env "hi"=none) :
    closeScope s ⟨FiniteScalarMachine.bind (FiniteScalarMachine.bind s.env "lo" a) "hi" b⟩=s := by
  rcases s with ⟨env⟩
  change env "lo"=none at hlo
  change env "hi"=none at hhi
  apply congrArg State.mk
  funext name
  by_cases lo : name="lo"
  · subst name; simp [closeScope,FiniteScalarMachine.bind,hlo]
  · by_cases hi : name="hi"
    · subst name; simp [closeScope,FiniteScalarMachine.bind,hhi]
    · simp only [closeScope,FiniteScalarMachine.bind,Function.update_of_ne lo,Function.update_of_ne hi]
      exact (show ∀x : Option Value,(if x.isSome then x else none)=x by
        intro x; cases x <;>rfl) (env name)

theorem final_scope (r : RawFactoredCell) :
    closeScope (FiniteCellExecution.input r) (withBoth r)=FiniteCellExecution.input r :=
  scope_two _ _ _ rfl rfl

theorem eval_compare_of {p : Prototypes} {c : Service} {s : State} {op : String}
    {a b : Expr} {x y result : Value}
    (kind : op="<" ∨ op="<=" ∨ op=">" ∨ op="==" ∨ op="!=")
    (left : FiniteScalarMachine.pure p c s.env 7 a=some x)
    (right : FiniteScalarMachine.pure p c s.env 7 b=some y)
    (answer : WideScalar.binary op x y=some result) :
    Eval p c (.binary op a b) s s result := by
  have computed := FiniteScalarMachine.pure_binary left right answer
  rcases kind with rfl|rfl|rfl|rfl|rfl
  all_goals
    change (do let v←FiniteScalarMachine.pure p c s.env 8 _;pure (s,v))=_
    rw [computed]
    rfl

theorem n_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary "<" (.var "n") (.nat 38358837683)) s s
      (WideScalar.boolean (decide (r.n<38358837683))) :=
  eval_compare_of (by simp)
    (FiniteScalarRules.pure_variable fields.nValue)
    (FiniteScalarRules.pure_literal (show literal 38358837683=some (FiniteCellWords.signedWord 64 38358837683) by rfl))
    (FiniteCellWords.u64_signed_lt fits.nWord (Or.inr rfl) (by decide))

theorem advance_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary "<=" (.var "next") (.var "n")) s s
      (WideScalar.boolean (decide (r.next≤r.n))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.nextValue)
    (FiniteScalarRules.pure_variable fields.nValue) (FiniteCellWords.u64_le fits.nextWord fits.nWord)

theorem upper_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary ">" (.var "next") (.nat 2000000000001)) s s
      (WideScalar.boolean (decide (2000000000001<r.next))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.nextValue)
    (FiniteScalarRules.pure_literal (show literal 2000000000001=some (FiniteCellWords.signedWord 64 2000000000001) by rfl))
    (FiniteCellWords.u64_signed_gt fits.nextWord (Or.inr rfl) (by decide))

theorem j_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary ">" (.var "j") (.var "n")) s s
      (WideScalar.boolean (decide (r.n<r.j))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.jValue)
    (FiniteScalarRules.pure_variable fields.nValue) (FiniteCellWords.u64_gt fits.jWord fits.nWord)

theorem q_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary ">" (.var "Q") (.var "j")) s s
      (WideScalar.boolean (decide (r.j<r.Q))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.qValue)
    (FiniteScalarRules.pure_variable fields.jValue) (FiniteCellWords.u64_gt fits.qWord fits.jWord)

theorem predecessor_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) (positive : 0<r.next) :
    FiniteScalarMachine.pure p c s.env 7 predecessor=some (word64 (r.next-1)) :=
  FiniteScalarMachine.pure_binary (FiniteScalarRules.pure_variable fields.nextValue)
    (FiniteScalarRules.pure_literal (show literal 1=some (i32 1) by rfl))
    (FiniteCellWords.u64_minus_one fits.nextWord positive)

theorem p_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) (positive : 0<r.next) :
    Eval p c (.binary ">" (.var "P") predecessor) s s
      (WideScalar.boolean (decide (r.next-1<r.P))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.pValue)
    (predecessor_pure fields fits positive)
    (FiniteCellWords.u64_gt fits.pWord ((Nat.sub_le _ _).trans_lt fits.nextWord))

theorem log_positive_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) :
    Eval p c (.binary "==" (.var "Lu") (.nat 0)) s s
      (WideScalar.boolean (decide (r.Lu=0))) :=
  eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.luValue)
    (FiniteScalarRules.pure_literal (show literal 0=some (i32 0) by rfl))
    (FiniteCellWords.u64_signed_eq fits.luWord (Or.inl rfl) (by decide))

theorem call_none {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name : String} {answer : Value} (response : invoke p c name []=some answer) :
    FiniteScalarMachine.pure p c env (fuel+1) (.call (.var name) [])=some answer := by
  simpa only [FiniteScalarMachine.pure,List.mapM,List.mapM.loop,Bind.bind,Option.bind,Pure.pure] using response

theorem call_one {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name arg : String} {value answer : Value} (lookup : env arg=some value)
    (response : invoke p c name [value]=some answer) :
    FiniteScalarMachine.pure p c env (fuel+2) (.call (.var name) [.var arg])=some answer := by
  simpa only [FiniteScalarMachine.pure,List.mapM,List.mapM.loop,lookup,Bind.bind,Option.bind,Pure.pure] using response

theorem log_eval {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r)
    (response : invoke FiniteCellExecution.prototypes FiniteCellExecution.service
      "rpc_log_upper" [word64 r.n]=some (word64 r.Lu)) :
    Eval FiniteCellExecution.prototypes FiniteCellExecution.service
      (.binary "!=" (.var "Lu") (.call (.var "rpc_log_upper") [.var "n"])) s s
      (WideScalar.boolean false) := by
  apply eval_compare_of (by simp) (FiniteScalarRules.pure_variable fields.luValue)
    (call_one fields.nValue response)
  simpa using FiniteCellWords.u64_ne fits.luWord fits.luWord

theorem low_response : invoke FiniteCellExecution.prototypes FiniteCellExecution.service
    "rpc_e_low" []=some (word64 eLo) := by
  unfold invoke FiniteCellExecution.prototypes FiniteCellExecution.service
  decide

theorem high_response : invoke FiniteCellExecution.prototypes FiniteCellExecution.service
    "rpc_e_high" []=some (word64 eHi) := by
  unfold invoke FiniteCellExecution.prototypes FiniteCellExecution.service
  decide

theorem cast_variable {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name : String} {n : Nat} (lookup : env name=some (word64 n)) (fits : n<2^64) :
    FiniteScalarMachine.pure p c env (fuel+2) (.cast "__uint128_t" (.var name))=some (word128 n) :=
  FiniteScalarRules.pure_cast rfl (FiniteScalarRules.pure_variable lookup)
    (FiniteScalarWords.word64_cast128 fits)

theorem j_product_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    {fuel : Nat} (fields : Inputs r s.env) (fits : WordFits r)
    (hi : s.env "hi"=some (word64 eHi)) :
    FiniteScalarMachine.pure p c s.env (fuel+3) jProduct=some (word128 (r.j*eHi)) :=
  FiniteScalarMachine.pure_binary (cast_variable fields.jValue fits.jWord)
    (FiniteScalarRules.pure_variable hi)
    (FiniteCellWords.u128_mul64 (fits.jWord.trans (by norm_num)) (by norm_num [eHi,eLo])
      (FinitePredicateBounds.word_product fits.jWord (by norm_num [eHi,eLo])))

theorem n_product_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    {fuel : Nat} (fields : Inputs r s.env) (fits : WordFits r) :
    FiniteScalarMachine.pure p c s.env (fuel+3) nProduct=some (word128 (r.n*2^60)) := by
  exact FiniteScalarMachine.pure_binary (cast_variable fields.nValue fits.nWord)
    (FiniteScalarRules.pure_literal (show literal 1152921504606846976=
      some (FiniteCellWords.signedWord 64 (2^60)) by rfl))
    (FiniteCellWords.u128_mul_signed (fits.nWord.trans (by norm_num)) (Or.inr rfl) (by norm_num)
      (FinitePredicateBounds.word_product fits.nWord (by norm_num)))

theorem j_exp_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r)
    (hi : s.env "hi"=some (word64 eHi)) :
    Eval p c (.binary ">" jProduct nProduct) s s
      (WideScalar.boolean (decide (r.n*2^60<r.j*eHi))) :=
  eval_compare_of (by simp) (j_product_pure fields fits hi) (n_product_pure fields fits)
    (FiniteCellWords.u128_gt (FinitePredicateBounds.word_product fits.jWord (by norm_num [eHi,eLo]))
      (FinitePredicateBounds.word_product fits.nWord (by norm_num)))

theorem quotient_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    {fuel : Nat} (fields : Inputs r s.env) (fits : WordFits r)
    (lo : s.env "lo"=some (word64 eLo)) (positive : 0<r.Lu) :
    FiniteScalarMachine.pure p c s.env (fuel+4) quotient=some (word128 ((r.n*eLo)/r.Lu)) :=
  FiniteScalarMachine.pure_binary
    (FiniteScalarMachine.pure_binary (cast_variable fields.nValue fits.nWord)
      (FiniteScalarRules.pure_variable lo)
      (FiniteCellWords.u128_mul64 (fits.nWord.trans (by norm_num)) (by norm_num [eLo])
        (FinitePredicateBounds.word_product fits.nWord (by norm_num [eLo]))))
    (FiniteScalarRules.pure_variable fields.luValue)
    (FiniteCellWords.u128_div64 (FinitePredicateBounds.word_product fits.nWord (by norm_num [eLo]))
      fits.luWord positive)

theorem a_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r)
    (lo : s.env "lo"=some (word64 eLo)) (positive : 0<r.Lu) :
    Eval p c (.binary "!=" (.cast "__uint128_t" (.var "A")) quotient) s s
      (WideScalar.boolean (decide (r.A≠(r.n*eLo)/r.Lu))) :=
  eval_compare_of (by simp) (cast_variable fields.aValue fits.aWord)
    (quotient_pure fields fits lo positive)
    (FiniteCellWords.u128_ne (fits.aWord.trans (by norm_num))
      (FinitePredicateBounds.quotient_u128 fits.nWord (by norm_num [eLo])))

theorem strict_left_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    {fuel : Nat} (fields : Inputs r s.env) (fits : WordFits r) (bound : r.P≤2000000000000) :
    FiniteScalarMachine.pure p c s.env (fuel+4) strictLeft=some (word128 ((2^20*r.P)*r.P)) := by
  have castScale : WideScalar.cast u128 (i32 1048576)=some (word128 (2^20)) := by decide
  exact FiniteScalarMachine.pure_binary
    (FiniteScalarMachine.pure_binary
      (FiniteScalarRules.pure_cast rfl (FiniteScalarRules.pure_literal (show literal 1048576=some (i32 1048576) by rfl)) castScale)
      (FiniteScalarRules.pure_variable fields.pValue)
      (FiniteCellWords.u128_mul64 (by norm_num) fits.pWord (FinitePredicateBounds.scaled_square bound).1))
    (FiniteScalarRules.pure_variable fields.pValue)
    (FiniteCellWords.u128_mul64 (FinitePredicateBounds.scaled_square bound).1 fits.pWord
      (FinitePredicateBounds.scaled_square bound).2)

theorem strict_right_pure {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    {fuel : Nat} (fields : Inputs r s.env) (fits : WordFits r) :
    FiniteScalarMachine.pure p c s.env (fuel+3) strictRight=some (word128 (r.A*r.Q)) :=
  FiniteScalarMachine.pure_binary (cast_variable fields.aValue fits.aWord)
    (FiniteScalarRules.pure_variable fields.qValue)
    (FiniteCellWords.u128_mul64 (fits.aWord.trans (by norm_num)) fits.qWord
      (FinitePredicateBounds.word_product fits.aWord fits.qWord))

theorem strict_eval {p : Prototypes} {c : Service} {r : RawFactoredCell} {s : State}
    (fields : Inputs r s.env) (fits : WordFits r) (bound : r.P≤2000000000000) :
    Eval p c strictExpr s s (WideScalar.boolean (decide ((2^20*r.P)*r.P<r.A*r.Q))) :=
  eval_compare_of (by simp) (strict_left_pure fields fits bound) (strict_right_pure fields fits)
    (FiniteCellWords.u128_lt (FinitePredicateBounds.scaled_square bound).2
      (FinitePredicateBounds.word_product fits.aWord fits.qWord))

#print axioms actual_body
#print axioms input_fields
#print axioms final_scope
#print axioms n_eval
#print axioms p_eval
end RamanujanPV.FiniteCellProtected
