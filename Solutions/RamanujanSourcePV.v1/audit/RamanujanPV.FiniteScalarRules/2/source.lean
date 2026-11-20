import RamanujanPV.FiniteScalarWords
namespace RamanujanPV.FiniteScalarRules
open FiniteScalarMachine FiniteScalarWords WideScalar
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option Elab.async false

structure Operands (width : Nat) (a b : FiniteScalarMachine.Value) : Prop where
  a_valid : InRange a.type a.number
  b_valid : InRange b.type b.number
  common_type : common a.type b.type=unsignedType width
  a_range : Range width a.number
  b_range : Range width b.number

def operation (width : Nat) (op : String) (x y : Int) : Option FiniteScalarMachine.Value :=
  if op == "+" then make (unsignedType width) (x+y)
  else if op == "-" then make (unsignedType width) (x-y)
  else if op == "*" then make (unsignedType width) (x*y)
  else if op == "/" then if y=0 then none else make (unsignedType width) (Int.tdiv x y)
  else if op == "%" then if y=0 then none else make (unsignedType width) (Int.tmod x y)
  else if op == "<" then some (boolean (x<y))
  else if op == "<=" then some (boolean (x≤y))
  else if op == ">" then some (boolean (x>y))
  else if op == ">=" then some (boolean (x≥y))
  else if op == "==" then some (boolean (x==y))
  else if op == "!=" then some (boolean (x != y))
  else none

theorem binary_reduce {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width)
    (h : Operands width a b) (op : String)
    (hop : op="+" ∨op="-" ∨op="*" ∨op="/" ∨op="%" ∨op="<" ∨op="<=" ∨
      op=">" ∨op=">=" ∨op="==" ∨op="!=") :
    binary op a b=operation width op a.number b.number := by
  have ca:=cast_number a hw h.a_range
  have cb:=cast_number b hw h.b_range
  simp only [binary,h.a_valid,h.b_valid,decide_true,Bool.not_true,Bool.false_or,
    Bool.false_eq_true,↓reduceIte,h.common_type,ca,cb,Option.bind]
  rcases hop with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    simp [operation,scalarWord,unsignedType]

theorem add {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b)
    (hab : Range width (a.number+b.number)) :
    binary "+" a b=some (scalarWord width (a.number+b.number)) := by
  rw [binary_reduce hw h "+" (Or.inl rfl)]
  exact make_exact hw hab

theorem sub {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b)
    (hab : Range width (a.number-b.number)) :
    binary "-" a b=some (scalarWord width (a.number-b.number)) := by
  rw [binary_reduce hw h "-" (by simp)]
  exact make_exact hw hab

theorem mul {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b)
    (hab : Range width (a.number*b.number)) :
    binary "*" a b=some (scalarWord width (a.number*b.number)) := by
  rw [binary_reduce hw h "*" (by simp)]
  exact make_exact hw hab

theorem div {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b)
    (hb : 0<b.number) :
    binary "/" a b=some (scalarWord width (a.number/b.number)) := by
  rw [binary_reduce hw h "/" (by simp)]
  simpa [operation,ne_of_gt hb,Int.tdiv_eq_ediv_of_nonneg h.a_range.1] using
    make_exact hw (quotient_range h.a_range hb)

theorem mod {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b)
    (hb : 0<b.number) :
    binary "%" a b=some (scalarWord width (a.number%b.number)) := by
  rw [binary_reduce hw h "%" (by simp)]
  have hm : Range width (a.number%b.number):=⟨Int.emod_nonneg _ (ne_of_gt hb),
    (Int.emod_lt_of_pos _ hb).trans h.b_range.2⟩
  simpa [operation,ne_of_gt hb,Int.tmod_eq_emod_of_nonneg h.a_range.1] using make_exact hw hm

theorem eq {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b) :
    binary "==" a b=some (boolean (a.number==b.number)) := by
  rw [binary_reduce hw h "==" (by simp)]
  rfl

theorem ne {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b) :
    binary "!=" a b=some (boolean (a.number != b.number)) := by
  rw [binary_reduce hw h "!=" (by simp)]
  rfl

theorem lt {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b) :
    binary "<" a b=some (boolean (a.number<b.number)) := by
  rw [binary_reduce hw h "<" (by simp)]
  rfl

theorem le {width : Nat} {a b : FiniteScalarMachine.Value} (hw : 0<width) (h : Operands width a b) :
    binary "<=" a b=some (boolean (a.number≤b.number)) := by
  rw [binary_reduce hw h "<=" (by simp)]
  rfl

theorem pure_variable {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {name : String} {v : FiniteScalarMachine.Value} (h:env name=some v) :
    FiniteScalarMachine.pure p c env (fuel+1) (.var name)=some v := h

theorem pure_literal {p : Prototypes} {c : Service} {env : Env} {fuel n : Nat}
    {v : FiniteScalarMachine.Value} (h:literal n=some v) : FiniteScalarMachine.pure p c env (fuel+1) (.nat n)=some v := h

theorem pure_cast {p : Prototypes} {c : Service} {env : Env} {fuel : Nat}
    {typeName : String} {type : CIntType} {e : Expr} {a b : FiniteScalarMachine.Value}
    (ht:namedType typeName=some type) (he:FiniteScalarMachine.pure p c env fuel e=some a)
    (hc:cast type a=some b) :
    FiniteScalarMachine.pure p c env (fuel+1) (.cast typeName e)=some b := by
  simp only [FiniteScalarMachine.pure,ht,he,Option.bind,hc]

#print axioms binary_reduce
#print axioms div
end RamanujanPV.FiniteScalarRules
