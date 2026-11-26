/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTAST
import FFTWordDivision
import FFTWordStore
import FFTLimbMultiplication
import FFTZeroParameters
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ProductRow
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots

def arrayAt (array index : String) : Expr := .index (.variable array) (.variable index)
def kExpr : Expr := .paren (.binary .add (.variable "i") (.variable "j"))
def tExpr : Expr := .paren (.binary .add
  (.paren (.binary .add (arrayAt "work" "k")
    (.paren (.binary .mul (arrayAt "a" "i") (arrayAt "b" "j"))))) (.variable "carry"))
def digitExpr : Expr := .paren (.binary .mod (.variable "t") (.literal (.integer 1000000000 "ULL")))
def carryExpr : Expr := .paren (.binary .div (.variable "t") (.literal (.integer 1000000000 "ULL")))
def digitStmt : Stmt := .assign (arrayAt "work" "k") digitExpr

def items : Stmt → List Stmt | .block xs=>xs | _=>[]
def whileBody : Stmt → Stmt | .whileLoop _ body=>body | _=>.block []
def actualInner : List Stmt := items (whileBody ((items (whileBody
  ((items fixed_multiply_ast.body).getD 2 (.block [])))).getD 2 (.block [])))

/-- Exact source-AST location, not a different demonstration program. -/
theorem actual_inner_shape : actualInner=[
    .declare .u64 "k" (some kExpr),.declare .u64 "t" (some tExpr),digitStmt,
    .assign (.variable "carry") carryExpr,ZeroLoop.increment] := by rfl

/-- Actual C expression, including all source parentheses and uint64 products.
The input premises are real source loads, not an assumed application output. -/
theorem source_t_eval {F : Type} (context : Context F) (before : State F)
    (a b d c : Nat) (ha : a<1000000000) (hb : b<1000000000)
    (hd : d<1000000000) (hc : c<1000000000)
    (readA : Eval context before (arrayAt "a" "i") (.integer (integer64 a)) before)
    (readB : Eval context before (arrayAt "b" "j") (.integer (integer64 b)) before)
    (readD : Eval context before (arrayAt "work" "k") (.integer (integer64 d)) before)
    (readC : Eval context before (.variable "carry") (.integer (integer64 c)) before) :
    Eval context before tExpr (.integer (integer64 (d+a*b+c))) before := by
  have ht:=schoolbook_digit_safe a b d c ha hb hd hc
  have hp : a*b<2^64 := by omega
  have hs : d+a*b<2^64 := by omega
  have mulWord : binary before .mul (.integer (integer64 a)) (.integer (integer64 b))=
      some (.integer (integer64 (a*b))) := by
    simp only [binary,binary64_mul a b (by omega) (by omega) hp,Option.map_some]
  have sumWord : binary before .add (.integer (integer64 d)) (.integer (integer64 (a*b)))=
      some (.integer (integer64 (d+a*b))) := by
    simp only [binary,binary64_add d (a*b) (by omega) hp hs,Option.map_some]
  have carryWord : binary before .add (.integer (integer64 (d+a*b))) (.integer (integer64 c))=
      some (.integer (integer64 (d+a*b+c))) := by
    simp only [binary,binary64_add (d+a*b) c hs (by omega) ht,Option.map_some]
  exact .paren (.binaryLR (.paren (.binaryLR readD
    (.paren (.binaryLR readA readB mulWord)) sumWord)) readC carryWord)

/-- Actual declaration of t, with fresh allocation and C conversion proved. -/
theorem source_t_declaration {F : Type} (context : Context F) (before : State F)
    (well : WellScoped before) (t : Nat) (ht : t<2^64)
    (evalT : Eval context before tExpr (.integer (integer64 t)) before) :
    ∃after,Exec context before (.declare .u64 "t" (some tExpr)) .normal after ∧
      Declaration before after "t" .u64 (.integer (integer64 t)) := by
  obtain ⟨after,decl⟩ := ZeroFrame.declare_exists well .u64 "t" _ (ZeroFrame.u64_storable t ht)
  exact ⟨after,.declareSome evalT decl,
    declare_storable (ZeroFrame.u64_storable t ht) (convert64 t ht) decl⟩

/-- The actual source digit store refines one mathematical row update. -/
theorem source_digit_store {F : Type} (context : Context F) {before : State F}
    {object length k t : Nat} {data : Nat→Nat}
    (rep : WordArrayRep before object length data) (hk : k<length) (ht : t<2^64)
    (readT : Eval context before (.variable "t") (.integer (integer64 t)) before)
    (placeWork : Place context before (arrayAt "work" "k") (wordPointer object k) before) :
    Exec context before digitStmt .normal
      {before with objects := fun key => if key=object then some (wordObject length (Function.update data k (t%1000000000))) else before.objects key} := by
  apply Exec.assign (value:=.integer (integer64 (t%1000000000)))
    (Eval.paren (Eval.binaryLR readT
      (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 1000000000)) (by rfl))
      (by simp only [binary,binary64_mod t 1000000000 ht (by norm_num) (by norm_num),Option.map_some])))
    placeWork
  exact word_store rep hk (lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num))


/-- Actual quotient expression used to advance the carry, with C division
and its positive divisor checked in the same word interpretation. -/
theorem source_carry_eval {F : Type} (context : Context F) (before : State F)
    (t : Nat) (ht : t<2^64)
    (readT : Eval context before (.variable "t") (.integer (integer64 t)) before) :
    Eval context before carryExpr (.integer (integer64 (t/1000000000))) before := by
  exact .paren (.binaryLR readT
    (.literal (.integer 1000000000 "ULL") _ (.integer (integer64 1000000000)) (by rfl))
    (by simp only [binary,binary64_div t 1000000000 ht (by norm_num) (by norm_num),Option.map_some]))

/-- The verified source store has the global numerical conservation law used
by row_value; no hardcoded product or assumed numerical trace occurs here. -/
theorem source_row_conservation (length k a b c : Nat) (data : Nat→Nat) (hk : k<length) :
    RH080Next.FFT.Limbs.value 1000000000 length
        (Function.update data k ((data k+a*b+c)%1000000000))+
      (((data k+a*b+c)/1000000000:Nat):Int)*(1000000000:Int)^(k+1)=
    RH080Next.FFT.Limbs.value 1000000000 length data+
      ((a*b+c:Nat):Int)*(1000000000:Int)^k := by
  rw [RH080Next.FFT.Limbs.value_update _ _ _ _ _ hk,pow_succ]
  have h : (((data k+a*b+c)%1000000000:Nat):Int)+
      1000000000*(((data k+a*b+c)/1000000000:Nat):Int)=
      (data k:Int)+(a:Int)*(b:Int)+(c:Int) := by
    exact_mod_cast Nat.mod_add_div (data k+a*b+c) 1000000000
  push_cast at h ⊢
  linear_combination (1000000000:Int)^k*h


/-- Actual source memory execution and the numerical row update are connected
in one theorem. This is one inner-row step, not a completed helper/FFT claim. -/
theorem source_digit_conservation {F : Type} (context : Context F) {before : State F}
    {object length k a b c : Nat} {data : Nat→Nat}
    (rep : WordArrayRep before object length data) (hk : k<length)
    (ha : a<1000000000) (hb : b<1000000000) (hd : data k<1000000000) (hc : c<1000000000)
    (readT : Eval context before (.variable "t") (.integer (integer64 (data k+a*b+c))) before)
    (placeWork : Place context before (arrayAt "work" "k") (wordPointer object k) before) :
    Exec context before digitStmt .normal
      {before with objects := fun key => if key=object then some (wordObject length
        (Function.update data k ((data k+a*b+c)%1000000000))) else before.objects key} ∧
    RH080Next.FFT.Limbs.value 1000000000 length
        (Function.update data k ((data k+a*b+c)%1000000000))+
      (((data k+a*b+c)/1000000000:Nat):Int)*(1000000000:Int)^(k+1)=
    RH080Next.FFT.Limbs.value 1000000000 length data+
      ((a*b+c:Nat):Int)*(1000000000:Int)^k := by
  exact ⟨source_digit_store context rep hk (schoolbook_digit_safe a b (data k) c ha hb hd hc)
    readT placeWork,source_row_conservation length k a b c data hk⟩

#print axioms source_carry_eval
#print axioms source_digit_conservation

#print axioms actual_inner_shape
#print axioms source_t_eval
#print axioms source_t_declaration
#print axioms source_digit_store
#print axioms source_row_conservation
end RH080Next.FFTPV.ProductRow
