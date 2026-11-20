/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteCellExecution
import RamanujanPV.FinitePredicateBounds
import RamanujanPV.FiniteScalarRules

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
    Inputs r (bind env name v) := by
  constructor
  · simpa [bind,Function.update_of_ne (Ne.symm hn)] using h.nValue
  · simpa [bind,Function.update_of_ne (Ne.symm hnext)] using h.nextValue
  · simpa [bind,Function.update_of_ne (Ne.symm hj)] using h.jValue
  · simpa [bind,Function.update_of_ne (Ne.symm hp)] using h.pValue
  · simpa [bind,Function.update_of_ne (Ne.symm hq)] using h.qValue
  · simpa [bind,Function.update_of_ne (Ne.symm hlu)] using h.luValue
  · simpa [bind,Function.update_of_ne (Ne.symm ha)] using h.aValue

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
  ⟨bind (FiniteCellExecution.input r).env "lo" (word64 eLo)⟩
def withBoth (r : RawFactoredCell) : State :=
  ⟨bind (withLow r).env "hi" (word64 eHi)⟩

theorem low_fields (r : RawFactoredCell) : Inputs r (withLow r).env :=
  (input_fields r).bind_other _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem both_fields (r : RawFactoredCell) : Inputs r (withBoth r).env :=
  (low_fields r).bind_other _ (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem final_scope (r : RawFactoredCell) :
    closeScope (FiniteCellExecution.input r) (withBoth r)=FiniteCellExecution.input r := by
  apply congrArg State.mk
  funext name
  by_cases lo : name="lo"
  · subst name; rfl
  · by_cases hi : name="hi"
    · subst name; rfl
    · simp only [closeScope,withBoth,withLow,bind,Function.update_of_ne lo,Function.update_of_ne hi]
      cases h : (FiniteCellExecution.input r).env name <;> rfl

#print axioms actual_body
#print axioms input_fields
#print axioms final_scope
end RamanujanPV.FiniteCellProtected
