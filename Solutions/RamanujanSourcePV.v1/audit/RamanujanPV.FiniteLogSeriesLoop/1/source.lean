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

def prefix (z z2 k : Nat) : Nat :=
  ∑ i ∈ Finset.range k, sourceCeilDiv (log20Power F z z2 i) (2*i+1)

lemma prefix_zero (z z2 : Nat) : prefix z z2 0=0 := by simp [prefix]
lemma prefix_succ (z z2 k : Nat) :
    prefix z z2 (k+1)=prefix z z2 k+sourceCeilDiv (log20Power F z z2 k) (2*k+1) := by
  simp [prefix,Finset.sum_range_succ]
lemma prefix_twenty (z z2 : Nat) : prefix z z2 20=log20Sum F z z2 := rfl

structure Reads (s : State) (z z2 k : Nat) : Prop where
  read_F : s.env "F"=some (word64 F)
  read_z : s.env "z"=some (word64 z)
  read_z2 : s.env "z2"=some (word64 z2)
  read_power : s.env "power"=some (word64 (log20Power F z z2 k))
  read_sum : s.env "sum"=some (word128 (prefix z z2 k))
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
    prefix z z2 k<2^128 := by
  have bound := FiniteLogBounds.prefix_sum_bound hz hz2 k
  change prefix z z2 k≤k*F at bound
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
  simp only [pure,List.mapM_cons,List.mapM_nil,hl,hr,Option.bind,Option.pure_def]
  exact called

def sumState (s : State) (z z2 k : Nat) : State :=
  ⟨FiniteScalarMachine.bind s.env "sum" (word128 (prefix z z2 (k+1)))⟩
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

#print axioms actual_source_subtree
#print axioms prefix_bound
#print axioms pure_call_two
#print axioms next_reads
end RamanujanPV.FiniteLogSeriesLoop
