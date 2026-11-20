import RamanujanPV.FiniteLogSeriesRules
import RamanujanPV.FiniteLogBounds
namespace RamanujanPV.FiniteLogSeriesInit
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
open AnalyticTransition LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false
abbrev F : Nat := 2^60
abbrev P := FiniteLogCeil.prototypes
abbrev C := FiniteLogServices.ceilService

def input (num den : Nat) : State := ⟨fun name=>
  if name="num" then some (word64 num) else if name="den" then some (word64 den) else none⟩
def withF (num den : Nat) : State := ⟨FiniteScalarMachine.bind (input num den).env "F" (word64 F)⟩
def withZ (num den : Nat) : State :=
  ⟨FiniteScalarMachine.bind (withF num den).env "z" (word64 (fixedLogZ num den))⟩
def withZ2 (num den : Nat) : State :=
  ⟨FiniteScalarMachine.bind (withZ num den).env "z2" (word64 (fixedLogZ2 num den))⟩
def withPower (num den : Nat) : State :=
  ⟨FiniteScalarMachine.bind (withZ2 num den).env "power" (word64 (fixedLogZ num den))⟩
def initialized (num den : Nat) : State :=
  ⟨FiniteScalarMachine.bind (withPower num den).env "sum" (word128 0)⟩

def zExpr : Expr := .call (.var "rpc_log_ceildiv")
  [.binary "*" (.cast "__uint128_t" (.var "F")) (.var "num"),.var "den"]
def z2Expr : Expr := .call (.var "rpc_log_ceildiv")
  [.binary "*" (.cast "__uint128_t" (.var "z")) (.var "z"),.var "F"]
def initialStatements : List Stmt := [
  .declare [⟨"uint64_t","F",some (.nat F)⟩],
  .declare [⟨"uint64_t","z",some zExpr⟩],
  .declare [⟨"uint64_t","z2",some z2Expr⟩],
  .declare [⟨"uint64_t","power",some (.var "z")⟩],
  .declare [⟨"__uint128_t","sum",some (.nat 0)⟩]]

theorem initial_source_subtree : (match FiniteLogSource.seriesFunction.body with
    | .sequence statements=>statements.take 5 | _=>[])=initialStatements := rfl

theorem declare_f (num den : Nat) : Declare P C
    [⟨"uint64_t","F",some (.nat F)⟩] (input num den) (withF num den) := by rfl

theorem z_pure {num den : Nat} (hd:0<den) (half:2*num≤den)
    (numBound:num≤2000000000000) (denWord:den<2^64) :
    pure P C (withF num den).env 8 zExpr=some (word64 (fixedLogZ num den)) := by
  have numWord:num<2^64 := numBound.trans_lt (by norm_num)
  have fWord : F<2^64 := by norm_num
  have product : F*num<2^128 := (FiniteLogBounds.wide_products hd half numBound).1
  have zWord : fixedLogZ num den<2^64 := (FiniteLogBounds.z_bound hd half).trans_lt (by norm_num)
  have fCast : pure P C (withF num den).env 6 (.cast "__uint128_t" (.var "F"))=
      some (word128 F) :=
    pure_cast rfl (pure_variable rfl) (word64_cast128 fWord)
  have multiplication : pure P C (withF num den).env 7
      (.binary "*" (.cast "__uint128_t" (.var "F")) (.var "num"))=
      some (word128 (F*num)) :=
    pure_binary fCast (pure_variable rfl)
      (FiniteCellWords.u128_mul64 (by norm_num : F<2^128) numWord product)
  have called : invoke P C "rpc_log_ceildiv" [word128 (F*num),word64 den]=
      some (word64 (fixedLogZ num den)) :=
    FiniteLogServices.invoke_ceil (cast128 product) (word64_cast128 denWord) product
      (denWord.trans (by norm_num)) hd zWord
  exact pure_call2 multiplication (pure_variable rfl) called

theorem z_declare {num den : Nat} (hd:0<den) (half:2*num≤den)
    (numBound:num≤2000000000000) (denWord:den<2^64) :
    Declare P C [⟨"uint64_t","z",some zExpr⟩] (withF num den) (withZ num den) :=
  declare_one_of rfl rfl (z_pure hd half numBound denWord)
    (cast64 ((FiniteLogBounds.z_bound hd half).trans_lt (by norm_num)))

theorem z2_pure {num den : Nat} (hd:0<den) (half:2*num≤den)
    (numBound:num≤2000000000000) :
    pure P C (withZ num den).env 8 z2Expr=some (word64 (fixedLogZ2 num den)) := by
  let z:=fixedLogZ num den
  have zWord : z<2^64 := (FiniteLogBounds.z_bound hd half).trans_lt (by norm_num)
  have z128 : z<2^128 := zWord.trans (by norm_num)
  have product : z*z<2^128 := by
    simpa only [z,pow_two] using (FiniteLogBounds.wide_products hd half numBound).2.1
  have z2Word : fixedLogZ2 num den<2^64 := (FiniteLogBounds.z2_bound hd half).trans_lt (by norm_num)
  have zCast : pure P C (withZ num den).env 6 (.cast "__uint128_t" (.var "z"))=
      some (word128 z) :=
    pure_cast rfl (pure_variable rfl) (word64_cast128 zWord)
  have multiplication : pure P C (withZ num den).env 7
      (.binary "*" (.cast "__uint128_t" (.var "z")) (.var "z"))=
      some (word128 (z*z)) :=
    pure_binary zCast (pure_variable rfl) (FiniteCellWords.u128_mul64 z128 zWord product)
  have called : invoke P C "rpc_log_ceildiv" [word128 (z*z),word64 F]=
      some (word64 (fixedLogZ2 num den)) := by
    simpa only [z,fixedLogZ2,pow_two] using
      (FiniteLogServices.invoke_ceil (cast128 product) (word64_cast128 (by norm_num : F<2^64))
        product (by norm_num : F<2^128) (by norm_num : 0<F)
        (show sourceCeilDiv (z*z) F<2^64 by simpa only [z,fixedLogZ2,pow_two] using z2Word))
  exact pure_call2 multiplication (pure_variable rfl) called

theorem z2_declare {num den : Nat} (hd:0<den) (half:2*num≤den)
    (numBound:num≤2000000000000) :
    Declare P C [⟨"uint64_t","z2",some z2Expr⟩] (withZ num den) (withZ2 num den) :=
  declare_one_of rfl rfl (z2_pure hd half numBound)
    (cast64 ((FiniteLogBounds.z2_bound hd half).trans_lt (by norm_num)))

theorem power_declare {num den : Nat} (hd:0<den) (half:2*num≤den) :
    Declare P C [⟨"uint64_t","power",some (.var "z")⟩] (withZ2 num den) (withPower num den) :=
  declare_one_of rfl rfl (pure_variable rfl)
    (cast64 ((FiniteLogBounds.z_bound hd half).trans_lt (by norm_num)))

theorem sum_declare (num den : Nat) :
    Declare P C [⟨"__uint128_t","sum",some (.nat 0)⟩] (withPower num den) (initialized num den) := by rfl

/-- Every temporary value is actually computed by its C declaration and the
source-proved helper; the initial source table/state is never assumed. -/
theorem initialization_executes {num den : Nat} (hd:0<den) (half:2*num≤den)
    (numBound:num≤2000000000000) (denWord:den<2^64) :
    SeqRun P C initialStatements (input num den) (.continuing (initialized num den)) := by
  exact LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (declare_f num den))
    (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (z_declare hd half numBound denWord))
    (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (z2_declare hd half numBound))
    (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (power_declare hd half))
    (LCMSourcePV.ASTLoops.SeqRun.next (LCMSourcePV.ASTLoops.StmtRun.declare (sum_declare num den))
      (LCMSourcePV.ASTLoops.SeqRun.nil _)))))

#print axioms initial_source_subtree
#print axioms initialization_executes
end RamanujanPV.FiniteLogSeriesInit
