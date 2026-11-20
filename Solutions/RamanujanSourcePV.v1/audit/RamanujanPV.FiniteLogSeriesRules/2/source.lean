import RamanujanPV.FiniteLogServices
import RamanujanPV.FiniteCellWords
namespace RamanujanPV.FiniteLogSeriesRules
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

theorem pure_call2 {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name : String} {a b : Expr} {left right result : Value}
    (ha:pure p c env fuel a=some left) (hb:pure p c env fuel b=some right)
    (call:invoke p c name [left,right]=some result) :
    pure p c env (fuel+1) (.call (.var name) [a,b])=some result := by
  simp only [FiniteScalarMachine.pure,List.mapM_cons,List.mapM_nil,ha,hb]
  change invoke p c name [left,right]=some result
  exact call

theorem declare_one_of {p : Prototypes} {c : Service} {s : State}
    {name typeName : String} {type : CIntType} {expression : Expr} {value converted : Value}
    (ht:namedType typeName=some type) (fresh:s.env name=none)
    (evaluated:pure p c s.env 8 expression=some value)
    (casted:WideScalar.cast type value=some converted) :
    Declare p c [⟨typeName,name,some expression⟩] s ⟨FiniteScalarMachine.bind s.env name converted⟩ := by
  change (do
    let type←namedType typeName
    if (s.env name).isSome then none else do
      let value←pure p c s.env 8 expression
      let converted←WideScalar.cast type value
      return State.mk (FiniteScalarMachine.bind s.env name converted))=some _
  rw [ht]
  change (if (s.env name).isSome then none else do
    let value←pure p c s.env 8 expression
    let converted←WideScalar.cast type value
    return State.mk (FiniteScalarMachine.bind s.env name converted))=some _
  rw [fresh]
  change (do let value←pure p c s.env 8 expression
             let converted←WideScalar.cast type value
             return State.mk (FiniteScalarMachine.bind s.env name converted))=some _
  rw [evaluated]
  change (do let converted←WideScalar.cast type value
             return State.mk (FiniteScalarMachine.bind s.env name converted))=some _
  rw [casted]
  rfl

theorem cast64 {n : Nat} (hn:n<2^64) :
    WideScalar.cast u64 (word64 n)=some (word64 n) :=
  cast_number _ (by decide : 0<64) (range_nat hn)

theorem cast128 {n : Nat} (hn:n<2^128) :
    WideScalar.cast u128 (word128 n)=some (word128 n) :=
  cast_number _ (by decide : 0<128) (range_nat hn)

theorem sub64 {a b : Nat} (ha:a<2^64) (hb:b<2^64) (hba:b≤a) :
    WideScalar.binary "-" (word64 a) (word64 b)=some (word64 (a-b)) := by
  have hr:=range_nat ((Nat.sub_le a b).trans_lt ha)
  have sub:=FiniteScalarRules.sub (by decide : 0<64) (FiniteCellWords.operands64 ha hb)
    (by simpa only [word64,Int.natCast_sub hba] using hr)
  simpa only [word64,scalarWord,unsignedType,u64,Int.natCast_sub hba] using sub

theorem add128_64 {a b : Nat} (ha:a<2^128) (hb:b<2^64) (hab:a+b<2^128) :
    WideScalar.binary "+" (word128 a) (word64 b)=some (word128 (a+b)) := by
  have sum:=FiniteScalarRules.add (by decide : 0<128) (FiniteCellWords.operands128_64 ha hb)
    (by simpa only [word128,word64,Int.natCast_add] using range_nat hab)
  simpa only [word128,word64,scalarWord,unsignedType,u128,Int.natCast_add] using sum

theorem signed_mul128 {a b : Nat} (ha:a<2^31) (hb:b<2^128) (hab:a*b<2^128) :
    WideScalar.binary "*" (i32 a) (word128 b)=some (word128 (a*b)) := by
  have operands : Operands 128 (i32 a) (word128 b) := by
    exact ⟨FiniteCellWords.signed_valid (by decide : 0<32) (by simpa using ha),
      scalar_range (by decide) (range_nat hb),by rfl,
      range_nat (ha.trans (by norm_num)),range_nat hb⟩
  have mul:=FiniteScalarRules.mul (by decide : 0<128) operands
    (by simpa only [i32,word128,Int.natCast_mul] using range_nat hab)
  simpa only [i32,word128,scalarWord,unsignedType,u128,Int.natCast_mul] using mul

#print axioms pure_call2
#print axioms declare_one_of
#print axioms sub64
#print axioms add128_64
end RamanujanPV.FiniteLogSeriesRules
