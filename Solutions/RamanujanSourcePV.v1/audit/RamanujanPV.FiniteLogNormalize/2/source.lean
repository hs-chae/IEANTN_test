/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.FiniteScalarRules
import RamanujanPV.FiniteLogSource
import RamanujanPV.FiniteLogNormalizationBounds

/-! Actual C execution of rpc_log_upper's normalization loop. Source syntax,
integer promotions, unsigned widths and scope effects are retained explicitly. -/
namespace RamanujanPV.FiniteLogNormalize
open LCMSourcePV.Witness.C LCMSourcePV.ASTLoops
open FiniteScalarMachine FiniteScalarWords FiniteScalarRules
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

def condition : Expr := .binary "<=" (.var "two") (.binary "/" (.var "n") (.nat 2))
def body : Stmt := .sequence [
  .eval (.binary "=" (.var "two") (.binary "*" (.var "two") (.nat 2))),
  .eval (.unary "++" (.var "k"))]
def normalization : Stmt := .whileLoop condition body

theorem actual_source_subtree :
    (match FiniteLogSource.upperFunction.body with
      | .sequence statements => statements[3]?
      | _ => none)=some normalization := rfl

lemma word_valid {n : Nat} (hn : n<2^64) :
    WideScalar.InRange (word64 n).type (word64 n).number :=
  scalar_range (by decide : 0<64) (range_nat hn)

lemma word_operands {a b : Nat} (ha : a<2^64) (hb : b<2^64) :
    Operands 64 (word64 a) (word64 b) :=
  ⟨word_valid ha,word_valid hb,rfl,range_nat ha,range_nat hb⟩

lemma two_operands {a : Nat} (ha : a<2^64) : Operands 64 (word64 a) (i32 2) :=
  ⟨word_valid ha,by decide +kernel,rfl,range_nat ha,by norm_num [Range,i32]⟩

lemma one_operands {a : Nat} (ha : a<2^64) : Operands 64 (word64 a) (i32 1) :=
  ⟨word_valid ha,by decide +kernel,rfl,range_nat ha,by norm_num [Range,i32]⟩

lemma word_div_two {a : Nat} (ha : a<2^64) :
    WideScalar.binary "/" (word64 a) (i32 2)=some (word64 (a/2)) := by
  have h:=FiniteScalarRules.div (by decide : 0<64) (two_operands ha) (by decide)
  have castDiv : (a:Int)/2=((a/2:Nat):Int) := by omega
  change WideScalar.binary "/" (word64 a) (i32 2)=some (scalarWord 64 ((a:Int)/2)) at h
  rw [castDiv] at h
  simpa [word64,scalarWord,unsignedType,u64] using h

lemma word_mul_two {a : Nat} (ha : a<2^64) (hnext : a*2<2^64) :
    WideScalar.binary "*" (word64 a) (i32 2)=some (word64 (a*2)) := by
  have range : Range 64 ((word64 a).number*(i32 2).number) := by
    constructor
    · simp only [word64,i32]; positivity
    · have bound : (a:Int)*2 < 2^64 := by exact_mod_cast hnext
      simpa only [word64,i32,Nat.cast_ofNat] using bound
  have h:=FiniteScalarRules.mul (by decide : 0<64) (two_operands ha) range
  simpa [word64,i32,scalarWord,unsignedType,u64,Nat.cast_mul] using h

lemma word_add_one {a : Nat} (ha : a<2^64) (hnext : a+1<2^64) :
    WideScalar.binary "+" (word64 a) (i32 1)=some (word64 (a+1)) := by
  have h:=FiniteScalarRules.add (by decide : 0<64) (one_operands ha)
    (show Range 64 ((word64 a).number+(i32 1).number) by
      simpa [word64,i32,Nat.cast_add] using range_nat hnext)
  simpa [word64,i32,scalarWord,unsignedType,u64,Nat.cast_add] using h

lemma word_le {a b : Nat} (ha : a<2^64) (hb : b<2^64) :
    WideScalar.binary "<=" (word64 a) (word64 b)=
      some (WideScalar.boolean (decide (a≤b))) := by
  simpa [word64] using FiniteScalarRules.le (by decide : 0<64) (word_operands ha hb)

lemma cast_word {n : Nat} (hn : n<2^64) :
    WideScalar.cast u64 (word64 n)=some (word64 n) := WideScalar.cast_same (word_valid hn)

lemma condition_pure {p : Prototypes} {c : Service} {s : State} {n two : Nat}
    (hn : s.env "n"=some (word64 n)) (ht : s.env "two"=some (word64 two))
    (nb : n<2^64) (tb : two<2^64) :
    pure p c s.env 8 condition=some (WideScalar.boolean (decide (two≤n/2))) := by
  have div : pure p c s.env 7 (.binary "/" (.var "n") (.nat 2))=some (word64 (n/2)) :=
    FiniteScalarMachine.pure_binary (pure_variable hn)
      (pure_literal (by decide +kernel : literal 2=some (i32 2))) (word_div_two nb)
  exact FiniteScalarMachine.pure_binary (pure_variable ht) div
    (word_le tb ((Nat.div_le_self n 2).trans_lt nb))

lemma condition_eval {p : Prototypes} {c : Service} {s : State} {n two : Nat}
    (hn : s.env "n"=some (word64 n)) (ht : s.env "two"=some (word64 two))
    (nb : n<2^64) (tb : two<2^64) :
    Eval p c condition s s (WideScalar.boolean (decide (two≤n/2))) := by
  change (do return (s,←pure p c s.env 8 condition))=some _
  rw [condition_pure hn ht nb tb]
  rfl

#print axioms actual_source_subtree
#print axioms condition_eval
end RamanujanPV.FiniteLogNormalize
