import RamanujanPV.FiniteScalarRules
import RamanujanPV.FiniteLogSource
import RamanujanPV.AnalyticTransition
namespace RamanujanPV.FiniteLogCeil
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

def prototypes : Prototypes := fun name=>
  if name="rpc_log_ceildiv" then some ⟨u64,[u128,u128]⟩
  else if name="rpc_log_series_upper" then some ⟨u64,[u64,u64]⟩
  else if name="rpc_log_upper" then some ⟨u64,[u64]⟩ else none

def noCalls : Service := fun _ _=>none

def input (a b : Nat) : State :=
  ⟨fun name=>if name="a" then some (word128 a) else
    if name="b" then some (word128 b) else none⟩

theorem operands128 {a b : Nat} (ha:a<2^128) (hb:b<2^128) :
    Operands 128 (word128 a) (word128 b) := by
  exact ⟨scalar_range (by decide) (range_nat ha),scalar_range (by decide) (range_nat hb),
    by rfl,range_nat ha,range_nat hb⟩

theorem operands128_zero {a : Nat} (ha:a<2^128) : Operands 128 (word128 a) (i32 0) := by
  exact ⟨scalar_range (by decide) (range_nat ha),by decide,by rfl,range_nat ha,by decide⟩

theorem boolean_valid (b : Bool) : WideScalar.InRange (WideScalar.boolean b).type
    (WideScalar.boolean b).number := by cases b <;>decide

theorem operands128_boolean {a : Nat} (ha:a<2^128) (b : Bool) :
    Operands 128 (word128 a) (WideScalar.boolean b) := by
  exact ⟨scalar_range (by decide) (range_nat ha),boolean_valid b,
    by cases b <;>rfl,range_nat ha,by cases b <;>decide⟩

/-- Actual source body, including C usual conversions,128-bit division/modulo,
32-bit Boolean increment, and the final64-bit cast. No helper oracle is used. -/
theorem function_executes {a b : Nat} (ha:a<2^128) (hb:b<2^128) (hb0:0<b)
    (hresult:AnalyticTransition.sourceCeilDiv a b<2^64) :
    Run prototypes noCalls FiniteLogSource.ceilFunction.body (input a b)
      (.returned (input a b) (word64 (AnalyticTransition.sourceCeilDiv a b))) := by
  have hbInt : (0:Int)<b := by exact_mod_cast hb0
  have divResult := FiniteScalarRules.div (by decide : 0<128) (operands128 ha hb) hbInt
  have modResult := FiniteScalarRules.mod (by decide : 0<128) (operands128 ha hb) hbInt
  have modBound : a%b<2^128 := (Nat.mod_lt a hb0).trans hb
  have quotientBound : a/b<2^128 := (Nat.div_le_self a b).trans_lt ha
  have neqResult := FiniteScalarRules.ne (by decide : 0<128) (operands128_zero modBound)
  have guardResult := FiniteScalarRules.eq (by decide : 0<128) (operands128_zero hb)
  have castResult : WideScalar.cast u64 (word128 (AnalyticTransition.sourceCeilDiv a b))=
      some (word64 (AnalyticTransition.sourceCeilDiv a b)) :=
    cast_number _ (by decide : 0<64) (range_nat hresult)
  have incEq : (WideScalar.boolean (((a:Int)%(b:Int)) != (0:Int))).number=
      ((if a%b=0 then 0 else 1 : Nat):Int) := by
    by_cases h:a%b=0
    · simp [WideScalar.boolean,←Int.natCast_mod,h]
    · have hh : ((a%b:Nat):Int)≠0 := by exact_mod_cast h
      simp [WideScalar.boolean,←Int.natCast_mod,hh,h]
  have sumEq : (word128 (a/b)).number+
      (WideScalar.boolean (((a:Int)%(b:Int)) != (0:Int))).number=
      (AnalyticTransition.sourceCeilDiv a b:Int) := by
    rw [incEq]
    simp [word128,AnalyticTransition.sourceCeilDiv,Nat.cast_add]
  have sumRange : Range 128 ((word128 (a/b)).number+
      (WideScalar.boolean (((a:Int)%(b:Int)) != (0:Int))).number) := by
    rw [sumEq]
    exact range_nat (hresult.trans (by norm_num))
  have addResult:=FiniteScalarRules.add (by decide : 0<128)
    (operands128_boolean quotientBound (((a:Int)%(b:Int)) != (0:Int))) sumRange
  have retEval : Eval prototypes noCalls
      (.cast "uint64_t" (.binary "+" (.binary "/" (.var "a") (.var "b"))
        (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0))))
      (input a b) (input a b) (word64 (AnalyticTransition.sourceCeilDiv a b)) := by
    simp only [Eval,eval,FiniteScalarMachine.pure,input]
    simp only [show literal 0=some (i32 0) from rfl,if_pos rfl,show ("b"="a")=False from by decide,
      ↓reduceIte,Bind.bind,Option.bind]
    rw [divResult,modResult]
    simp only [word128,scalarWord,Int.natCast_div,Int.natCast_mod] at neqResult addResult ⊢
    rw [neqResult]
    simp only [Bind.bind,Option.bind]
    rw [addResult]
    simp only [Bind.bind,Option.bind]
    rw [sumEq] at castResult ⊢
    exact congrArg (fun result=>result.map (fun v=>(input a b,v))) castResult
  have guardEval : Eval prototypes noCalls (.binary "==" (.var "b") (.nat 0))
      (input a b) (input a b) (WideScalar.boolean false) := by
    simp only [Eval,eval,FiniteScalarMachine.pure,input]
    simp only [show literal 0=some (i32 0) from rfl,show ("b"="a")=False from by decide,
      ↓reduceIte,if_pos rfl,Bind.bind,Option.bind]
    rw [guardResult]
    simp [word128,ne_of_gt hbInt]
  apply LCMSourcePV.ASTLoops.StmtRun.sequence
    (inner:=.returned (input a b) (word64 (AnalyticTransition.sourceCeilDiv a b)))
  · apply LCMSourcePV.ASTLoops.SeqRun.next
    · exact LCMSourcePV.ASTLoops.StmtRun.branch guardEval (by
        change Run prototypes noCalls .skip _ _
        exact LCMSourcePV.ASTLoops.StmtRun.skip _)
    · exact LCMSourcePV.ASTLoops.SeqRun.returned
        (LCMSourcePV.ASTLoops.StmtRun.returnValue retEval)
  · change _=_.returned _ _
    simp only [closeFlow,close_scope_self]

#print axioms function_executes
end RamanujanPV.FiniteLogCeil
