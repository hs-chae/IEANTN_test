import RamanujanPV.FiniteLogCeil
namespace RamanujanPV.FiniteLogServices
open FiniteScalarMachine FiniteScalarWords
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

/-- This modular response is justified below by executing the actual source
helper. It is not an assumed mathematical oracle or a hardcoded output table. -/
def ceilService : Service := fun name args=>
  if name="rpc_log_ceildiv" then match args with
    | [a,b] =>
      if a.type=u128 ∧b.type=u128 ∧0≤a.number ∧0<b.number ∧
          a.number<2^128 ∧b.number<2^128 ∧
          AnalyticTransition.sourceCeilDiv a.number.toNat b.number.toNat<2^64
      then some (word64 (AnalyticTransition.sourceCeilDiv a.number.toNat b.number.toNat))
      else none
    | _ => none
  else none

def sourceInput (args : List Value) : State := match args with
  | [a,b]=>⟨fun name=>if name="a" then some a else if name="b" then some b else none⟩
  | _=>empty

/-- EVERY accepted modular response is realized by the complete source helper
on precisely the converted actual arguments. -/
theorem ceil_service_closed {name : String} {args : List Value} {answer : Value}
    (response : ceilService name args=some answer) :
    name="rpc_log_ceildiv" ∧
    ∃t,Run FiniteLogCeil.prototypes FiniteLogCeil.noCalls FiniteLogSource.ceilFunction.body
      (sourceInput args) (.returned t answer) := by
  by_cases hn:name="rpc_log_ceildiv"
  · subst name
    cases args with
    | nil => simp [ceilService] at response
    | cons a rest =>
      cases rest with
      | nil => simp [ceilService] at response
      | cons b tail =>
        cases tail with
        | cons c tail => simp [ceilService] at response
        | nil =>
          simp only [ceilService,↓reduceIte] at response
          split at response
          next h =>
            rcases h with ⟨atype,btype,an,bn,ar,br,cr⟩
            have av : a=word128 a.number.toNat := by
              cases a with
              | mk type number =>
                simp only at atype an ⊢
                cases atype
                simp only [word128,Int.toNat_of_nonneg an]
            have bv : b=word128 b.number.toNat := by
              cases b with
              | mk type number =>
                simp only at btype bn ⊢
                cases btype
                simp only [word128,Int.toNat_of_nonneg bn.le]
            have ha:a.number.toNat<2^128 := by omega
            have hb:b.number.toNat<2^128 := by omega
            have hb0:0<b.number.toNat := by omega
            have out : answer=word64 (AnalyticTransition.sourceCeilDiv a.number.toNat b.number.toNat) :=
              (Option.some.inj response).symm
            refine ⟨rfl,FiniteLogCeil.input a.number.toNat b.number.toNat,?_⟩
            rw [out]
            have inputEqual : sourceInput [a,b]=FiniteLogCeil.input a.number.toNat b.number.toNat := by
              rw [av,bv]
              rfl
            rw [inputEqual]
            exact FiniteLogCeil.function_executes ha hb hb0 cr
          next h => contradiction
  · simp [ceilService,hn] at response

/-- C argument conversion is performed by invoke; this lemma establishes a
single actual helper call, with both source-domain and narrow-result bounds. -/
theorem invoke_ceil {a b : Nat} {left right : Value}
    (ca:WideScalar.cast u128 left=some (word128 a))
    (cb:WideScalar.cast u128 right=some (word128 b))
    (ha:a<2^128) (hb:b<2^128) (hb0:0<b)
    (hr:AnalyticTransition.sourceCeilDiv a b<2^64) :
    invoke FiniteLogCeil.prototypes ceilService "rpc_log_ceildiv" [left,right]=
      some (word64 (AnalyticTransition.sourceCeilDiv a b)) := by
  have an : (0:Int)≤a := by omega
  have bn : (0:Int)<b := by exact_mod_cast hb0
  have ar : (a:Int)<2^128 := by exact_mod_cast ha
  have br : (b:Int)<2^128 := by exact_mod_cast hb
  have castOut : WideScalar.cast u64 (word64 (AnalyticTransition.sourceCeilDiv a b))=
      some (word64 (AnalyticTransition.sourceCeilDiv a b)) := cast_number _ (by decide) (range_nat hr)
  have argsConverted : convertArguments [u128,u128] [left,right]=some [word128 a,word128 b] := by
    simp only [convertArguments]
    rw [ca]
    change (do let v←WideScalar.cast u128 right; return [word128 a,v])=_
    rw [cb]
    rfl
  have serviceResult : ceilService "rpc_log_ceildiv" [word128 a,word128 b]=
      some (word64 (AnalyticTransition.sourceCeilDiv a b)) := by
    simp only [ceilService,↓reduceIte,word128,Int.toNat_natCast]
    simp only [u128,an,bn,ar,br,hr,and_self,↓reduceIte]
  change ((convertArguments [u128,u128] [left,right]).bind (fun args=>
    (ceilService "rpc_log_ceildiv" args).bind (WideScalar.cast u64)))=_
  rw [argsConverted]
  change ((ceilService "rpc_log_ceildiv" [word128 a,word128 b]).bind (WideScalar.cast u64))=_
  rw [serviceResult]
  exact castOut

#print axioms ceil_service_closed
#print axioms invoke_ceil
end RamanujanPV.FiniteLogServices
