/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ExplicitFFTQuadModel
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080Next.FFTPV.QuadSource
open GoldbachDirect GoldbachDirect.Semantics WordArrays SourceLocals SourceScalarSlots SourceBindings
open InputLoader RootSource

inductive Aux where | temp | quad | status deriving DecidableEq

def auxName : Aux → String | .temp=>"temp" | .quad=>"quad" | .status=>"status"
def auxType : Aux → CType | .temp | .quad=>.pointer .u64 | .status=>.u64

def auxValues (workObject : Nat) : Aux → Value
  | .temp=>.pointer (wordPointer workObject 160)
  | .quad=>.pointer (wordPointer workObject 208)
  | .status=>.integer (integer64 0)

def absoluteBranch : Stmt:=.ite magnitudeTest (.block [positiveAssignment]) (some (.block [negativeAssignment]))
def magnitudeStatement : Stmt:=.expression (.call "magnitude_into" [.variable "temp",.variable "value"])
def factorExpression : Expr:=.paren (.binary .mul (.paren (.binary .mul (.literal (.integer 20 "ULL")) (.variable "j"))) (.variable "j"))
def multiplyStatement : Stmt:=StatusCall.statement "multiply_small" [.variable "temp",.literal (.integer 5 "ULL"),factorExpression]
def addStatement : Stmt:=StatusCall.statement "add_magnitude" [.variable "quad",.variable "temp",.literal (.integer 6 "ULL")]
def rowStatements : List Stmt:=[eDeclaration,valueDeclaration,absoluteBranch,magnitudeStatement,multiplyStatement,addStatement,advanceStatement]
def loopBody : Stmt:=.block rowStatements

def loop (p : Profile) : Stmt:=.whileLoop (.binary .lt (.variable "j") (.literal (.integer p.count "ULL"))) loopBody

theorem actual_fap_loop : (ProductRow.items FapFFTRecursivePV.fap_recursive_norm_upper_ast.body)[34]?=some (loop .fap):=rfl
theorem actual_w4_loop : (ProductRow.items FFTRecursivePV.w4_recursive_norm_upper_ast.body)[35]?=some (loop .w4):=rfl

def absoluteValues (input : InputLoader.Input) (j : Nat) : InputLoader.Var → Value:=
  Function.update (plannedValues input j) (.inr .value) (.integer (integer64 (coefficientAbs input.profile j)))

/-- Real borrowed main locals and actual typed work/data buffers. Only the
already-declared variables are present; no future e/value slot is assumed. -/
structure View {F : Type} (state : State F) (input : InputLoader.Input) (workObject fo bo count j cutoff : Nat)
    (ids : InputLoader.Var → Nat) (auxIds : Aux → Nat) (values : InputLoader.Var → Value)
    (dataMemory workData : Nat → Nat) (pending : Bool:=false) : Prop where
  body : BodyView state input fo bo count j cutoff ids values dataMemory
  aux : Locals state auxName auxType auxIds fo (auxValues workObject)
  work : WordArrayRep state workObject 512 workData
  different : input.object≠workObject
  workSeparate : ∀v,Active count v → workObject≠ids v
  auxSeparate : ∀v,workObject≠auxIds v
  auxOld : ∀v,auxIds v< cutoff
  cross : ∀p v,ids (.inl p)≠auxIds v
  quadDigits : ∀d<6,workData (208+d)< base
  quadValue : FFT.Limbs.magnitude base 6 (fun d=> workData (208+d))=partialQuad input.profile j+(if pending then term input.profile j else 0)

#print axioms actual_fap_loop
#print axioms actual_w4_loop
end RH080Next.FFTPV.QuadSource
