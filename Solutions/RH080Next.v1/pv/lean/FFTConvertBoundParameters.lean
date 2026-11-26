/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import FFTConvertBoundLoop
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.ConvertBoundSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays
open SourceLocals SourceScalarSlots SourceBindings

def paramIds (baseId : Nat) : Var→Nat | .a=>baseId | .n=>baseId+1 | .i=>baseId+2

private theorem slot_declare_other {F : Type} {before after : State F}
    {id owner : Nat} {oldtype newtype : CType} {oldvalue newvalue : Value} {cname : String}
    (h : Slot before id owner oldtype oldvalue)
    (d : Declaration before after cname newtype newvalue)
    (different : id≠before.nextObject) : Slot after id owner oldtype oldvalue :=
  ⟨h.storable,by rw [d.outside id different];exact h.object⟩

/-- Both actual parameters and i=2 are born through the real declaration
semantics; no initial application locals are supplied. -/
theorem initialize_parameters {F : Type} {entry : State F}
    {object size start : Nat} {data : Nat→Nat}
    (well : WellScoped entry) (emptyEnv : entry.environment=[])
    (array : WordArrayRep entry object size data) (bound : start+6≤size)
    (digits : ∀k,k<6 → data (start+k)<base) :
    ∃sa sn si,
      entry.declare (.pointer .u64) "a" (some (.pointer (wordPointer object start)))=some sa ∧
      sa.declare .u64 "n" (some (.integer (integer64 6)))=some sn ∧
      sn.declare .u64 "i" (some (.integer (integer64 2)))=some si ∧
      View si object size start (paramIds entry.nextObject) entry.scope data 2 := by
  obtain ⟨sa,da⟩ := ZeroFrame.declare_exists well _ "a" _ (CompareSource.pointer_storable object start)
  have wa := wellScoped_declare well da
  obtain ⟨sn,dn⟩ := ZeroFrame.declare_exists wa _ "n" _ (ZeroFrame.u64_storable 6 (by norm_num))
  have wn := wellScoped_declare wa dn
  obtain ⟨si,di⟩ := ZeroFrame.declare_exists wn _ "i" _ (ZeroFrame.u64_storable 2 (by norm_num))
  have ia := declare_storable (CompareSource.pointer_storable object start) (CompareSource.pointer_storable object start).converted da
  have inum := declare_storable (ZeroFrame.u64_storable 6 (by norm_num)) (ZeroFrame.u64_storable 6 (by norm_num)).converted dn
  have ii := declare_storable (ZeroFrame.u64_storable 2 (by norm_num)) (ZeroFrame.u64_storable 2 (by norm_num)).converted di
  have oa := ia.nextObject
  have onum := inum.nextObject
  have sca := ia.scope
  have scn := inum.scope
  have old : object<entry.nextObject := well.objectIds _ _ array.2.1
  have lm : Locals si name type (paramIds entry.nextObject) entry.scope (values object start 2) := by
    constructor
    · intro v
      cases v <;> simp [paramIds,name,type,ii.environment,inum.environment,ia.environment,
        emptyEnv,oa,onum,scalarPointer,List.lookup]
    · intro v
      cases v with
      | a =>
        have h1 := slot_declare_other ia.slot inum (by omega)
        have h2 := slot_declare_other h1 ii (by omega)
        simpa only [paramIds,type,values] using h2
      | n =>
        have h1 := slot_declare_other inum.slot ii (by omega)
        simpa only [paramIds,type,values,oa,sca] using h1
      | i => simpa only [paramIds,type,values,oa,onum,sca,scn] using ii.slot
    · intro v w h
      cases v <;> cases w <;> simp_all [paramIds] <;> omega
    · rw [ii.nextScope,inum.nextScope,ia.nextScope]
      exact well.current
  have host : si.mode=.host := ii.mode.trans (inum.mode.trans (ia.mode.trans array.1))
  refine ⟨sa,sn,si,da,dn,di,⟨host,?_,array.2.2⟩,lm,?_,bound,digits,by norm_num,wellScoped_declare wn di⟩
  · rw [ii.outside object (by omega),inum.outside object (by omega),ia.outside object (by omega)]
    exact array.2.1
  · intro v;cases v <;> simp only [paramIds] <;> omega

theorem lower_lt {data : Nat→Nat} {start : Nat}
    (digits : ∀k,k<6 → data (start+k)<base) : lower data start<base^2 := by
  have h0 := digits 0 (by norm_num)
  have h1 := digits 1 (by norm_num)
  simp only [Nat.add_zero] at h0
  dsimp [lower,base] at *
  omega

theorem result_fits (data : Nat→Nat) (start : Nat)
    (digits : ∀k,k<6 → data (start+k)<base) : result data start<2^64 := by
  have h := lower_lt digits
  dsimp [result]
  split <;> dsimp [base,sentinel] at * <;> omega

def lowerExpression : Expr := match returnLower with
  | .returnValue (some e)=>e
  | _=>.literal (.integer 0 "ULL")

theorem lower_eval {F : Type} (context : Context F) {before : State F}
    {object size start owner i : Nat} {ids : Var→Nat} {data : Nat→Nat}
    (h : View before object size start ids owner data i) :
    Eval context before lowerExpression (.integer (integer64 (lower data start))) before := by
  have index0 : Eval context before (.index (.variable "a") (.literal (.integer 0 "ULL")))
      (.integer (integer64 (data start))) before := by
    have load := slice_word_load h.array (start:=start) (i:=0) (by have b:=h.bound;omega)
    exact .load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
      (.literal (.integer 0 "ULL") _ (.integer (integer64 0)) (by rfl)) (by simpa using slice_pointer_add h.array (start:=start) (i:=0) (by have b:=h.bound;omega))) (by simpa using load)
  have index1 : Eval context before (.index (.variable "a") (.literal (.integer 1 "ULL")))
      (.integer (integer64 (data (start+1)))) before := by
    exact .load (.index (.variable (h.locals.lookup Var.a) (h.locals.read Var.a))
      (.literal (.integer 1 "ULL") _ (.integer (integer64 1)) (by rfl)) (slice_pointer_add h.array (by have b:=h.bound;omega)))
      (word_load h.array (by have b:=h.bound;omega))
  have h0 := h.digits 0 (by norm_num)
  have h1 := h.digits 1 (by norm_num)
  have hl := lower_lt h.digits
  simp only [Nat.add_zero] at h0
  have mul : Integer.binary .mul (integer64 base) (integer64 (data (start+1)))=some (integer64 (base*data (start+1))) :=
    binary64_mul _ _ (by norm_num [base]) (by dsimp [base] at h1;omega) (by dsimp [lower,base] at hl ⊢;omega)
  have add : Integer.binary .add (integer64 (data start)) (integer64 (base*data (start+1)))=some (integer64 (lower data start)) :=
    binary64_add _ _ (by dsimp [base] at h0;omega) (by dsimp [lower,base] at hl ⊢;omega) (by dsimp [lower,base] at hl ⊢;omega)
  have mulEval : Eval context before (.paren (.binary .mul (.literal (.integer base "ULL"))
      (.index (.variable "a") (.literal (.integer 1 "ULL")))))
      (.integer (integer64 (base*data (start+1)))) before :=
    .paren (.binaryLR (.literal (.integer base "ULL") _ (.integer (integer64 base)) (by rfl)) index1
      (by simp only [binary,mul,Option.map_some]))
  exact .paren (.binaryLR index0 mulEval (by simp only [binary,add,Option.map_some]))

#print axioms initialize_parameters
#print axioms result_fits
#print axioms lower_eval
end RH080Next.FFTPV.ConvertBoundSource
