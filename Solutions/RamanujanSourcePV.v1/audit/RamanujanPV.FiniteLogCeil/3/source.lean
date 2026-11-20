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
  exact ⟨scalar_range (by decide) (range_nat ha),by decide,by rfl,range_nat ha,by norm_num [Range,i32]⟩

theorem boolean_valid (b : Bool) : WideScalar.InRange (WideScalar.boolean b).type
    (WideScalar.boolean b).number := by cases b <;>decide

theorem operands128_boolean {a : Nat} (ha:a<2^128) (b : Bool) :
    Operands 128 (word128 a) (WideScalar.boolean b) := by
  exact ⟨scalar_range (by decide) (range_nat ha),boolean_valid b,
    by cases b <;>rfl,range_nat ha,by cases b <;>norm_num [Range,WideScalar.boolean]⟩

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
  have quotientOp : WideScalar.binary "/" (word128 a) (word128 b)=some (word128 (a/b)) := by
    simpa only [word128,scalarWord,unsignedType,u128,Int.natCast_div] using divResult
  have remainderOp : WideScalar.binary "%" (word128 a) (word128 b)=some (word128 (a%b)) := by
    simpa only [word128,scalarWord,unsignedType,u128,Int.natCast_mod] using modResult
  have neqOp : WideScalar.binary "!=" (word128 (a%b)) (i32 0)=
      some (WideScalar.boolean ((a%b) != 0)) := by
    have hcast : (((a:Int)%(b:Int)) != (0:Int))=((a%b) != 0) := by
      rw [←Int.natCast_mod]
      by_cases h:a%b=0
      · simp [h]
      · have hh : ((a%b:Nat):Int)≠0 := by exact_mod_cast h
        simp [h,hh]
    simpa only [word128,i32,Int.natCast_mod,hcast] using neqResult
  have incEq : (WideScalar.boolean ((a%b) != 0)).number=
      ((if a%b=0 then 0 else 1 : Nat):Int) := by
    by_cases h:a%b=0 <;>simp [WideScalar.boolean,h]
  have sumEq : (word128 (a/b)).number+(WideScalar.boolean ((a%b) != 0)).number=
      (AnalyticTransition.sourceCeilDiv a b:Int) := by
    rw [incEq]
    simp [word128,AnalyticTransition.sourceCeilDiv,Nat.cast_add]
  have sumRange : Range 128 ((word128 (a/b)).number+
      (WideScalar.boolean ((a%b) != 0)).number) := by
    rw [sumEq]
    exact range_nat (hresult.trans (by norm_num))
  have addOp : WideScalar.binary "+" (word128 (a/b)) (WideScalar.boolean ((a%b) != 0))=
      some (word128 (AnalyticTransition.sourceCeilDiv a b)) := by
    have addResult:=FiniteScalarRules.add (by decide : 0<128)
      (operands128_boolean quotientBound ((a%b) != 0)) sumRange
    rw [sumEq] at addResult
    exact addResult
  have qEval : FiniteScalarMachine.pure prototypes noCalls (input a b).env 6
      (.binary "/" (.var "a") (.var "b"))=some (word128 (a/b)) :=
    pure_binary (pure_variable rfl) (pure_variable (by simp [input])) quotientOp
  have mEval : FiniteScalarMachine.pure prototypes noCalls (input a b).env 5
      (.binary "%" (.var "a") (.var "b"))=some (word128 (a%b)) :=
    pure_binary (pure_variable rfl) (pure_variable (by simp [input])) remainderOp
  have nEval : FiniteScalarMachine.pure prototypes noCalls (input a b).env 6
      (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0))=
      some (WideScalar.boolean ((a%b) != 0)) :=
    pure_binary mEval (pure_literal rfl) neqOp
  have sEval : FiniteScalarMachine.pure prototypes noCalls (input a b).env 7
      (.binary "+" (.binary "/" (.var "a") (.var "b"))
        (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0)))=
      some (word128 (AnalyticTransition.sourceCeilDiv a b)) :=
    pure_binary qEval nEval addOp
  have rEval := pure_cast (p:=prototypes) (c:=noCalls) (env:=(input a b).env)
    (typeName:="uint64_t") (by rfl) sEval castResult
  have retEval : Eval prototypes noCalls
      (.cast "uint64_t" (.binary "+" (.binary "/" (.var "a") (.var "b"))
        (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0))))
      (input a b) (input a b) (word64 (AnalyticTransition.sourceCeilDiv a b)) := by
    change ((FiniteScalarMachine.pure prototypes noCalls (input a b).env 8
      (.cast "uint64_t" (.binary "+" (.binary "/" (.var "a") (.var "b"))
        (.binary "!=" (.binary "%" (.var "a") (.var "b")) (.nat 0))))).bind
      (fun v=>some (input a b,v)))=_
    rw [rEval]
    rfl
  have guardOp : WideScalar.binary "==" (word128 b) (i32 0)=
      some (WideScalar.boolean false) := by
    simpa [word128,i32,ne_of_gt hbInt] using guardResult
  have gEval : FiniteScalarMachine.pure prototypes noCalls (input a b).env 8
      (.binary "==" (.var "b") (.nat 0))=some (WideScalar.boolean false) :=
    pure_binary (pure_variable (by simp [input])) (pure_literal rfl) guardOp
  have guardEval : Eval prototypes noCalls (.binary "==" (.var "b") (.nat 0))
      (input a b) (input a b) (WideScalar.boolean false) := by
    change ((FiniteScalarMachine.pure prototypes noCalls (input a b).env 8
      (.binary "==" (.var "b") (.nat 0))).bind (fun v=>some (input a b,v)))=_
    rw [gEval]
    rfl
  apply LCMSourcePV.ASTLoops.StmtRun.sequence
    (inner:=.returned (input a b) (word64 (AnalyticTransition.sourceCeilDiv a b)))
  · apply LCMSourcePV.ASTLoops.SeqRun.next
    · exact LCMSourcePV.ASTLoops.StmtRun.branch guardEval (by
        change Run prototypes noCalls .skip _ _
        exact LCMSourcePV.ASTLoops.StmtRun.skip _)
    · exact LCMSourcePV.ASTLoops.SeqRun.returned
        (LCMSourcePV.ASTLoops.StmtRun.returnValue retEval)
  · change _=closeFlow (input a b) (.returned (input a b) _)
    simp only [closeFlow,close_scope_self]

#print axioms function_executes
end RamanujanPV.FiniteLogCeil
