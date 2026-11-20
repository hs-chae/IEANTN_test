import RamanujanPV.FiniteLogSeriesInit
namespace RamanujanPV.FiniteLogSeriesReturn
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
open AnalyticTransition LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false
abbrev F : Nat := 2^60
abbrev P := FiniteLogCeil.prototypes
abbrev C := FiniteLogServices.ceilService

def numerator : Expr := .binary "*"
  (.binary "*" (.cast "__uint128_t" (.nat 2)) (.var "power")) (.var "F")
def denominator : Expr := .binary "*" (.cast "__uint128_t" (.nat 41))
  (.binary "-" (.var "F") (.var "z2"))
def tailExpr : Expr := .call (.var "rpc_log_ceildiv") [numerator,denominator]
def finalExpr : Expr := .cast "uint64_t"
  (.binary "+" (.binary "*" (.nat 2) (.var "sum")) tailExpr)

theorem actual_source_return : (match FiniteLogSource.seriesFunction.body with
    | .sequence statements=>statements[6]? | _=>none)=some (.returnStmt finalExpr) := rfl

structure Reads (s : State) (z z2 : Nat) : Prop where
  read_F : s.env "F"=some (word64 F)
  read_z2 : s.env "z2"=some (word64 z2)
  read_power : s.env "power"=some (word64 (log20Power F z z2 20))
  read_sum : s.env "sum"=some (word128 (log20Sum F z z2))

theorem numerator_pure {s : State} {z z2 : Nat} (reads:Reads s z z2)
    (hz:z≤2^59) (hz2:z2≤2^59) :
    pure P C s.env 5 numerator=some (word128 (2*log20Power F z z2 20*F)) := by
  have powerBound:=FiniteLogBounds.power_bound hz hz2 20
  have powerWord : log20Power F z z2 20<2^64 := powerBound.trans_lt (by norm_num)
  have double : 2*log20Power F z z2 20<2^128 := by norm_num at powerBound ⊢;omega
  have product : 2*log20Power F z z2 20*F<2^128 := by norm_num [F] at powerBound ⊢;nlinarith
  have twoCast : pure P C s.env 3 (.cast "__uint128_t" (.nat 2))=some (word128 2) :=
    pure_cast rfl (pure_literal rfl) (by rfl)
  have timesTwo : pure P C s.env 4
      (.binary "*" (.cast "__uint128_t" (.nat 2)) (.var "power"))=
      some (word128 (2*log20Power F z z2 20)) :=
    pure_binary twoCast (pure_variable reads.read_power)
      (FiniteCellWords.u128_mul64 (by norm_num) powerWord double)
  exact pure_binary timesTwo (pure_variable reads.read_F)
    (FiniteCellWords.u128_mul64 double (by norm_num : F<2^64) product)

theorem denominator_pure {s : State} {z z2 : Nat} (reads:Reads s z z2)
    (hz2:z2≤2^59) :
    pure P C s.env 5 denominator=some (word128 (41*(F-z2))) := by
  have z2Word : z2<2^64 := hz2.trans_lt (by norm_num)
  have z2F : z2≤F := hz2.trans (by norm_num)
  have difference : F-z2<2^64 := (Nat.sub_le F z2).trans_lt (by norm_num)
  have product : 41*(F-z2)<2^128 := by
    have bound:=Nat.sub_le F z2
    norm_num [F] at bound ⊢
    omega
  have fortyoneCast : pure P C s.env 4 (.cast "__uint128_t" (.nat 41))=some (word128 41) :=
    pure_cast rfl (pure_literal rfl) (by rfl)
  have differenceEval : pure P C s.env 4 (.binary "-" (.var "F") (.var "z2"))=
      some (word64 (F-z2)) :=
    pure_binary (pure_variable reads.read_F) (pure_variable reads.read_z2)
      (sub64 (by norm_num) z2Word z2F)
  exact pure_binary fortyoneCast differenceEval
    (FiniteCellWords.u128_mul64 (by norm_num) difference product)

theorem tail_pure {s : State} {z z2 : Nat} (reads:Reads s z z2)
    (hz:z≤2^59) (hz2:z2≤2^59) :
    pure P C s.env 6 tailExpr=some (word64
      (sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2)))) := by
  have powerBound:=FiniteLogBounds.power_bound hz hz2 20
  have num : 2*log20Power F z z2 20*F<2^128 := by norm_num [F] at powerBound ⊢;nlinarith
  have den : 41*(F-z2)<2^128 := by
    have bound:=Nat.sub_le F z2
    norm_num [F] at bound ⊢
    omega
  have tailWord : sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2))<2^64 :=
    (FiniteLogBounds.tail_bound hz hz2).trans_lt (by norm_num [FiniteLogBounds.F])
  have called:=FiniteLogServices.invoke_ceil (cast128 num) (cast128 den) num den
    (FiniteLogBounds.tail_denominator hz2).2 tailWord
  exact pure_call2 (numerator_pure reads hz hz2) (denominator_pure reads hz2) called

/-- The ACTUAL final C expression: both left-associated128-bit products,
unsigned64 subtraction, source helper division, mixed-width sum and final
uint64 narrowing are proved exact before applying the analytic series theorem. -/
theorem return_pure {s : State} {z z2 : Nat} (reads:Reads s z z2)
    (hz:z≤2^59) (hz2:z2≤2^59) :
    pure P C s.env 8 finalExpr=some (word64 (log20Output F z z2)) := by
  have sumBound:=FiniteLogBounds.sum_bound hz hz2
  have total : log20Sum F z z2<2^128 := sumBound.trans_lt (by norm_num)
  have double : 2*log20Sum F z z2<2^128 := by norm_num at sumBound ⊢;omega
  have tailWord : sourceCeilDiv (2*log20Power F z z2 20*F) (41*(F-z2))<2^64 :=
    (FiniteLogBounds.tail_bound hz hz2).trans_lt (by norm_num [FiniteLogBounds.F])
  have outputWord : log20Output F z z2<2^64 :=
    (FiniteLogBounds.output_bound hz hz2).trans_lt (by norm_num [FiniteLogBounds.F])
  have doubleEval : pure P C s.env 6 (.binary "*" (.nat 2) (.var "sum"))=
      some (word128 (2*log20Sum F z z2)) :=
    pure_binary (pure_literal rfl) (pure_variable reads.read_sum)
      (signed_mul128 (by norm_num : 2<2^31) total double)
  have added : pure P C s.env 7 (.binary "+" (.binary "*" (.nat 2) (.var "sum")) tailExpr)=
      some (word128 (log20Output F z z2)) :=
    pure_binary doubleEval (tail_pure reads hz hz2)
      (add128_64 double tailWord (outputWord.trans (by norm_num)))
  exact pure_cast rfl added
    (cast_number _ (by decide : 0<64) (range_nat outputWord))

theorem return_eval {s : State} {z z2 : Nat} (reads:Reads s z z2)
    (hz:z≤2^59) (hz2:z2≤2^59) :
    Eval P C finalExpr s s (word64 (log20Output F z z2)) := by
  change ((pure P C s.env 8 finalExpr).bind (fun v=>some (s,v)))=_
  rw [return_pure reads hz hz2]
  rfl

#print axioms actual_source_return
#print axioms return_eval
end RamanujanPV.FiniteLogSeriesReturn
