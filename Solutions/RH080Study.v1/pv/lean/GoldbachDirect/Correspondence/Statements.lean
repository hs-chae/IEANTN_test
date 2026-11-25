import GoldbachDirect.Correspondence.Expressions

/-! Independent statement and translation-unit grammar for the actual application subset.
Expressions and identifiers are parameters, allowing their separate character/precedence
theorems to be composed without defining syntax as equality to an AST renderer.

Labels are not standalone C++ statements. The block-item judgment binds each flat proof-AST
label to its following executable statement. No rule admits a terminal label, a declaration
immediately following a label, an arbitrary function body, or arbitrary qualifier strings.
-/
namespace GoldbachDirect.Correspondence

abbrev ObjectType (t : CType) : Prop := t ≠ .void ∧ t ≠ .const .void

def objectTypeGuard (t : CType) : Bool :=
  typeSyntaxSafe t && decide (ObjectType t)

inductive AssignmentTarget : Expr → Prop
  | variable (name) : AssignmentTarget (.variable name)
  | index (base offset) : AssignmentTarget (.index base offset)
  | dereference (value) : AssignmentTarget (.unary .dereference value)
  | paren {value} : AssignmentTarget value → AssignmentTarget (.paren value)

def targetGuard : Expr → Bool
  | .variable _ | .index .. | .unary .dereference _ => true
  | .paren value => targetGuard value
  | _ => false

/-- Bodies whose final token cannot capture a subsequent else. The application uses only
compound bodies and explicit gotos as controlled substatements. -/
inductive Delimited : Stmt → Prop
  | block (items) : Delimited (.block items)
  | gotoLabel (name) : Delimited (.gotoLabel name)

def delimitedGuard : Stmt → Bool
  | .block _ | .gotoLabel _ => true
  | _ => false

def executableGuard : Stmt → Bool
  | .declare .. | .label _ => false
  | _ => true

def Executable (s : Stmt) : Prop :=
  (∀ t n e, s ≠ .declare t n e) ∧ (∀ n, s ≠ .label n)

/-- Comma-separated expressions, including the empty argument list. -/
inductive ArgumentsSyntax (E : List String → Expr → Prop) :
    List String → List Expr → Prop
  | nil : ArgumentsSyntax E [] []
  | singleton {ts e} : E ts e → ArgumentsSyntax E ts [e]
  | cons {ts e rest args} : E ts e → ArgumentsSyntax E rest args → args ≠ [] →
      ArgumentsSyntax E (ts ++ [","] ++ rest) (e :: args)

mutual
/-- A complete ordinary statement, with expressions parsed by the separate precedence grammar. -/
inductive StatementSyntax (E : List String → Expr → Prop) (N : String → Prop) :
    List String → Stmt → Prop
  | block {ts items} : ItemsSyntax E N ts items →
      StatementSyntax E N (["{"] ++ ts ++ ["}"]) (.block items)
  | declare {tt t n} : TypeSyntax tt t → ObjectType t → N n →
      StatementSyntax E N (tt ++ [n, ";"]) (.declare t n none)
  | initialize {tt t n et e} : TypeSyntax tt t → ObjectType t → N n → E et e →
      StatementSyntax E N (tt ++ [n, "="] ++ et ++ [";"]) (.declare t n (some e))
  | assign {dt d et e} : E dt d → AssignmentTarget d → E et e →
      StatementSyntax E N (dt ++ ["="] ++ et ++ [";"]) (.assign d e)
  | expression {ts e} : E ts e → StatementSyntax E N (ts ++ [";"]) (.expression e)
  | ifThen {ct c yt y} : E ct c → StatementSyntax E N yt y → Delimited y →
      StatementSyntax E N (["if", "("] ++ ct ++ [")"] ++ yt) (.ite c y none)
  | ifElse {ct c yt y nt n} : E ct c → StatementSyntax E N yt y →
      Delimited y → StatementSyntax E N nt n → Delimited n →
      StatementSyntax E N (["if", "("] ++ ct ++ [")"] ++ yt ++ ["else"] ++ nt)
        (.ite c y (some n))
  | whileLoop {ct c bt b} : E ct c → StatementSyntax E N bt b → Delimited b →
      StatementSyntax E N (["while", "("] ++ ct ++ [")"] ++ bt) (.whileLoop c b)
  | returnVoid : StatementSyntax E N ["return", ";"] (.returnValue none)
  | returnValue {ts e} : E ts e →
      StatementSyntax E N (["return"] ++ ts ++ [";"]) (.returnValue (some e))
  | gotoLabel {n} : N n → StatementSyntax E N ["goto", n, ";"] (.gotoLabel n)
  | launch {n gt g bt b ht h st s ats args} : N n → E gt g → E bt b → E ht h →
      E st s → ArgumentsSyntax E ats args →
      StatementSyntax E N ([n, "<<<"] ++ gt ++ [","] ++ bt ++ [","] ++ ht ++ [","] ++
        st ++ [">>>", "("] ++ ats ++ [")", ";"]) (.launch n g b h s args)

/-- A compound-statement's declaration/statement sequence. Labels attach to the next statement;
the source-side grammar never admits `name:` by itself. -/
inductive ItemsSyntax (E : List String → Expr → Prop) (N : String → Prop) :
    List String → List Stmt → Prop
  | nil : ItemsSyntax E N [] []
  | cons {st s ts items} : StatementSyntax E N st s → ItemsSyntax E N ts items →
      ItemsSyntax E N (st ++ ts) (s :: items)
  | labeled {n st s ts items} : N n → Executable s → StatementSyntax E N st s →
      ItemsSyntax E N ts items →
      ItemsSyntax E N ([n, ":"] ++ st ++ ts) (.label n :: s :: items)
end

mutual
def statementGuard (exprOK : Expr → Bool) (nameOK : String → Bool) : Nat → Stmt → Bool
  | 0, _ => false
  | fuel + 1, .block body => itemsGuard exprOK nameOK fuel body
  | _ + 1, .declare t n value => objectTypeGuard t && nameOK n &&
      value.toList.all exprOK
  | _ + 1, .assign d e => targetGuard d && exprOK d && exprOK e
  | _ + 1, .expression e => exprOK e
  | fuel + 1, .ite c y n => exprOK c && delimitedGuard y &&
      statementGuard exprOK nameOK fuel y && n.toList.all
        (fun b => delimitedGuard b && statementGuard exprOK nameOK fuel b)
  | fuel + 1, .whileLoop c b => exprOK c && delimitedGuard b &&
      statementGuard exprOK nameOK fuel b
  | _ + 1, .returnValue e => e.toList.all exprOK
  | _ + 1, .gotoLabel n => nameOK n
  | _ + 1, .launch n g b h s args => nameOK n &&
      ([g, b, h, s] ++ args).all exprOK
  | _ + 1, _ => false
def itemsGuard (exprOK : Expr → Bool) (nameOK : String → Bool) : Nat → List Stmt → Bool
  | 0, _ => false
  | _ + 1, [] => true
  | fuel + 1, .label n :: s :: rest => nameOK n && executableGuard s &&
      statementGuard exprOK nameOK fuel s && itemsGuard exprOK nameOK fuel rest
  | _ + 1, [.label _] => false
  | fuel + 1, s :: rest => statementGuard exprOK nameOK fuel s &&
      itemsGuard exprOK nameOK fuel rest
end

inductive QualifiersSyntax : List String → List Qualifier → Prop
  | plain : QualifiersSyntax [] []
  | local : QualifiersSyntax ["static"] [.static]
  | kernel : QualifiersSyntax ["__global__"] [.global]

def qualifiersGuard : List Qualifier → Bool
  | [] | [.static] | [.global] => true
  | _ => false

inductive ParametersSyntax (N : String → Prop) :
    List String → List (CType × String) → Prop
  | nil : ParametersSyntax N [] []
  | singleton {tt t n} : TypeSyntax tt t → ObjectType t → N n →
      ParametersSyntax N (tt ++ [n]) [(t, n)]
  | cons {tt t n rest ps} : TypeSyntax tt t → ObjectType t → N n →
      ParametersSyntax N rest ps → ps ≠ [] →
      ParametersSyntax N (tt ++ [n, ","] ++ rest) ((t, n) :: ps)

/-- Function definitions require an actual compound-statement body. -/
inductive FunctionSyntax (E : List String → Expr → Prop) (N : String → Prop) :
    List String → Function → Prop
  | ordinary {qts qs rts result n pts ps its items emptyVoid} :
      QualifiersSyntax qts qs → TypeSyntax rts result → N n →
      ParametersSyntax N pts ps → ItemsSyntax E N its items →
      (emptyVoid = false ∨ ps ≠ []) →
      FunctionSyntax E N (qts ++ rts ++ [n, "("] ++ pts ++ [")", "{"] ++ its ++ ["}"])
        ⟨qs, emptyVoid, result, n, ps, .block items⟩
  | voidParameters {qts qs rts result n its items} :
      QualifiersSyntax qts qs → TypeSyntax rts result → N n → ItemsSyntax E N its items →
      FunctionSyntax E N (qts ++ rts ++ [n, "(", "void", ")", "{"] ++ its ++ ["}"])
        ⟨qs, true, result, n, [], .block items⟩

def functionGuard (exprOK : Expr → Bool) (nameOK : String → Bool) (f : Function) : Bool :=
  qualifiersGuard f.qualifiers && typeSyntaxSafe f.result && nameOK f.name &&
    f.parameters.all (fun p => objectTypeGuard p.1 && nameOK p.2) &&
    (match f.body with
    | .block body => itemsGuard exprOK nameOK 1024 body
    | _ => false)

inductive HeaderSyntax : List String → Header → Prop
  | stdint : HeaderSyntax ["<", "stdint", ".", "h", ">"] .stdint
  | stddef : HeaderSyntax ["<", "stddef", ".", "h", ">"] .stddef
  | stdbool : HeaderSyntax ["<", "stdbool", ".", "h", ">"] .stdbool
  | stdlib : HeaderSyntax ["<", "stdlib", ".", "h", ">"] .stdlib
  | stdio : HeaderSyntax ["<", "stdio", ".", "h", ">"] .stdio
  | inttypes : HeaderSyntax ["<", "inttypes", ".", "h", ">"] .inttypes
  | cudaRuntime : HeaderSyntax ["<", "cuda_runtime", ".", "h", ">"] .cudaRuntime
  | primes : HeaderSyntax ["\"primes.h\""] .primes
  | kernels : HeaderSyntax ["\"kernels.cuh\""] .kernels

inductive TopSyntax (E : List String → Expr → Prop) (N : String → Prop) :
    List String → Top → Prop
  | include {ts h} : HeaderSyntax ts h → TopSyntax E N (["#", "include"] ++ ts) (.include h)
  | pragmaOnce : TopSyntax E N ["#", "pragma", "once"] .pragmaOnce
  | function {ts f} : FunctionSyntax E N ts f → TopSyntax E N ts (.function f)

inductive ProgramSyntax (E : List String → Expr → Prop) (N : String → Prop) :
    List String → Program → Prop
  | nil : ProgramSyntax E N [] []
  | cons {ts t rest p} : TopSyntax E N ts t → ProgramSyntax E N rest p →
      ProgramSyntax E N (ts ++ rest) (t :: p)

def programGuard (exprOK : Expr → Bool) (nameOK : String → Bool) (p : Program) : Bool :=
  p.all fun top => match top with
    | .include _ | .pragmaOnce => true
    | .function f => functionGuard exprOK nameOK f

end GoldbachDirect.Correspondence
