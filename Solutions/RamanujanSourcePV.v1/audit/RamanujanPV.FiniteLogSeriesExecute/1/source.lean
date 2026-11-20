import RamanujanPV.FiniteLogSeriesReturn
import RamanujanPV.FiniteLogSeriesLoop
namespace RamanujanPV.FiniteLogSeriesExecute
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules FiniteLogSeriesRules
open AnalyticTransition LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false
abbrev P := FiniteLogCeil.prototypes
abbrev C := FiniteLogServices.ceilService
abbrev F : Nat := 2^60

def series_input := FiniteLogSeriesInit.input

def withK (num den : Nat) : State :=
  ⟨FiniteScalarMachine.bind (FiniteLogSeriesInit.initialized num den).env "k" (word64 0)⟩

theorem initial_loop_reads (num den : Nat) :
    FiniteLogSeriesLoop.Reads (withK num den) (fixedLogZ num den) (fixedLogZ2 num den) 0 := by
  constructor <;>try rfl
  · change some (word128 0)=some (word128 _)
    rw [FiniteLogSeriesLoop.prefix_zero]

theorem actual_body : FiniteLogSource.seriesFunction.body=.sequence
    (FiniteLogSeriesInit.initialStatements++[FiniteLogSeriesLoop.sourceFor,
      .returnStmt FiniteLogSeriesReturn.finalExpr]) := rfl

theorem close_function_scope {num den : Nat} {t : State}
    (numRead:t.env "num"=some (word64 num)) (denRead:t.env "den"=some (word64 den)) :
    closeScope (series_input num den) t=series_input num den := by
  apply congrArg State.mk
  funext name
  by_cases hn:name="num"
  · subst name;simp [series_input,FiniteLogSeriesInit.input,closeScope,numRead]
  · by_cases hd:name="den"
    · subst name;simp [series_input,FiniteLogSeriesInit.input,closeScope,denRead]
    · simp [series_input,FiniteLogSeriesInit.input,closeScope,hn,hd]

/-- Complete source refinement for EVERY normalized uint64 parameter pair.
All source declarations,20 iterations, actual helper calls, final tail and
both lexical scopes are executed; no precomputed output is an input premise. -/
theorem function_executes {num den : Nat} (numWord:num<2^64) (denWord:den<2^64)
    (hd:0<den) (half:2*num≤den) :
    Run P C FiniteLogSource.seriesFunction.body (series_input num den)
      (.returned (series_input num den) (word64 (fixedLogSeries num den))) := by
  let z:=fixedLogZ num den
  let z2:=fixedLogZ2 num den
  have hz:z≤2^59:=FiniteLogBounds.z_bound hd half
  have hz2:z2≤2^59:=FiniteLogBounds.z2_bound hd half
  obtain ⟨t,loop,reads,frame⟩:=FiniteLogSeriesLoop.loop_exec hz hz2
    (by decide : 0≤20) (initial_loop_reads num den)
  let final:=closeScope (FiniteLogSeriesInit.initialized num den) t
  have initialized_k : Declare P C [⟨"uint64_t","k",some (.nat 0)⟩]
      (FiniteLogSeriesInit.initialized num den) (withK num den) := by rfl
  have forRun : Run P C FiniteLogSeriesLoop.sourceFor
      (FiniteLogSeriesInit.initialized num den) (.continuing final) :=
    LCMSourcePV.ASTLoops.StmtRun.forLoop
      (LCMSourcePV.ASTLoops.StmtRun.declare initialized_k) loop (by rfl)
  have finalReads : FiniteLogSeriesReturn.Reads final z z2 := by
    constructor
    · change t.env "F"=some (word64 F)
      exact reads.read_F
    · change t.env "z2"=some (word64 z2)
      exact reads.read_z2
    · change t.env "power"=some (word64 (log20Power F z z2 20))
      exact reads.read_power
    · change t.env "sum"=some (word128 (log20Sum F z z2))
      simpa only [FiniteLogSeriesLoop.prefix_twenty] using reads.read_sum
  have finalNum : final.env "num"=some (word64 num) := by
    change t.env "num"=some (word64 num)
    rw [frame "num" (by decide) (by decide) (by decide)]
    rfl
  have finalDen : final.env "den"=some (word64 den) := by
    change t.env "den"=some (word64 den)
    rw [frame "den" (by decide) (by decide) (by decide)]
    rfl
  have exitScope:=close_function_scope finalNum finalDen
  have returned:=FiniteLogSeriesReturn.return_eval finalReads hz hz2
  rw [actual_body]
  apply LCMSourcePV.ASTLoops.StmtRun.sequence
    (inner:=.returned final (word64 (fixedLogSeries num den)))
  · exact LCMSourcePV.ASTLoops.SeqRun.next
      (LCMSourcePV.ASTLoops.StmtRun.declare (FiniteLogSeriesInit.declare_f num den))
      (LCMSourcePV.ASTLoops.SeqRun.next
        (LCMSourcePV.ASTLoops.StmtRun.declare (FiniteLogSeriesInit.z_declare hd half numWord denWord))
      (LCMSourcePV.ASTLoops.SeqRun.next
        (LCMSourcePV.ASTLoops.StmtRun.declare (FiniteLogSeriesInit.z2_declare hd half numWord))
      (LCMSourcePV.ASTLoops.SeqRun.next
        (LCMSourcePV.ASTLoops.StmtRun.declare (FiniteLogSeriesInit.power_declare hd half))
      (LCMSourcePV.ASTLoops.SeqRun.next
        (LCMSourcePV.ASTLoops.StmtRun.declare (FiniteLogSeriesInit.sum_declare num den))
      (LCMSourcePV.ASTLoops.SeqRun.next forRun
        (LCMSourcePV.ASTLoops.SeqRun.returned (LCMSourcePV.ASTLoops.StmtRun.returnValue returned)))))))
  · change .returned (series_input num den) _=closeFlow (series_input num den) (.returned final _)
    simp only [closeFlow,exitScope]

theorem completed_correct {num den : Nat} {t : State} {answer : Value}
    (numWord:num<2^64) (denWord:den<2^64) (hd:0<den) (half:2*num≤den)
    (run:Run P C FiniteLogSource.seriesFunction.body (series_input num den) (.returned t answer)) :
    t=series_input num den ∧answer=word64 (fixedLogSeries num den) :=
  LCMSourcePV.ASTLoops.Flow.returned.inj (run_unique run (function_executes numWord denWord hd half))

/-- A closed modular function contract. Its output is justified for EVERY
accepted response by the complete generic source theorem above. -/
def service : Service := fun name args=>
  if name="rpc_log_series_upper" then match args with
    | [a,b]=>if a.type=u64 ∧b.type=u64 ∧0≤a.number ∧0<b.number ∧
        a.number<2^64 ∧b.number<2^64 ∧2*a.number.toNat≤b.number.toNat
      then some (word64 (fixedLogSeries a.number.toNat b.number.toNat)) else none
    | _=>none
  else FiniteLogServices.ceilService name args

theorem invoke_series {num den : Nat} {left right : Value}
    (ca:WideScalar.cast u64 left=some (word64 num))
    (cb:WideScalar.cast u64 right=some (word64 den))
    (numWord:num<2^64) (denWord:den<2^64) (hd:0<den) (half:2*num≤den) :
    invoke P service "rpc_log_series_upper" [left,right]=some (word64 (fixedLogSeries num den)) := by
  have argsConverted : convertArguments [u64,u64] [left,right]=some [word64 num,word64 den] := by
    simp only [convertArguments]
    rw [ca]
    change (do let v←WideScalar.cast u64 right;return [word64 num,v])=_
    rw [cb]
    rfl
  have an:(0:Int)≤num:=by omega
  have bn:(0:Int)<den:=by exact_mod_cast hd
  have ar:(num:Int)<2^64:=by exact_mod_cast numWord
  have br:(den:Int)<2^64:=by exact_mod_cast denWord
  have served : service "rpc_log_series_upper" [word64 num,word64 den]=
      some (word64 (fixedLogSeries num den)) := by
    simp only [service,↓reduceIte,word64,Int.toNat_natCast]
    simp only [an,bn,ar,br,half,and_self,↓reduceIte]
  have casted:=cast64 (FiniteLogBounds.fixed_series_u64 hd half)
  change ((convertArguments [u64,u64] [left,right]).bind (fun args=>
    (service "rpc_log_series_upper" args).bind (WideScalar.cast u64)))=_
  rw [argsConverted]
  change ((service "rpc_log_series_upper" [word64 num,word64 den]).bind (WideScalar.cast u64))=_
  rw [served]
  exact casted

theorem invoke_ceil {a b : Nat} {left right : Value}
    (ca:WideScalar.cast u128 left=some (word128 a))
    (cb:WideScalar.cast u128 right=some (word128 b))
    (ha:a<2^128) (hb:b<2^128) (hb0:0<b)
    (hr:sourceCeilDiv a b<2^64) :
    invoke P service "rpc_log_ceildiv" [left,right]=some (word64 (sourceCeilDiv a b)) := by
  change invoke P C "rpc_log_ceildiv" [left,right]=_
  exact FiniteLogServices.invoke_ceil ca cb ha hb hb0 hr

#print axioms function_executes
#print axioms completed_correct
#print axioms invoke_series
end RamanujanPV.FiniteLogSeriesExecute
