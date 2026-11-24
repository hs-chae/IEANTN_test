import WitnessCGrammar
import RamanujanPV.QuotientDriverSource

/-! Independent character syntax for the actual finite-counter C11 fragment.
No judgment below mentions a renderer, tokenizer, token equality or execution
result. Fully parenthesized compound expressions and matched statements make
precedence and dangling-else attachment explicit. Header interpretation, C
typing/conversions and adequacy of the execution model are separate contracts. -/
namespace RHOcticPush.CounterSyntax
open LCMSourcePV.Witness.C

def asciiLetter (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

def reserved : List String := ["auto", "break", "case", "char", "const", "continue",
  "default", "do", "double", "else", "enum", "extern", "float", "for", "goto", "if",
  "inline", "int", "long", "register", "restrict", "return", "short", "signed",
  "sizeof", "static", "struct", "switch", "typedef", "union", "unsigned", "void",
  "volatile", "while", "_Alignas", "_Alignof", "_Atomic", "_Bool", "_Complex",
  "_Generic", "_Imaginary", "_Noreturn", "_Static_assert", "_Thread_local", "_Pragma",
  "uint64_t"]

def Identifier (name : String) : Prop :=
  match name.toList with
  | [] => False
  | c::cs => asciiLetter c = true ∧
      cs.all (fun d => asciiLetter d || ('0' ≤ d && d ≤ '9') || d == '_') = true ∧
      name ∉ reserved

instance (name : String) : Decidable (Identifier name) := by
  unfold Identifier
  split <;> infer_instance

def BindingName (name : String) : Prop := Identifier name ∧
  name ∉ ["stdout", "stdin", "stderr", "fwrite", "fflush"]

instance (name : String) : Decidable (BindingName name) := by
  unfold BindingName
  infer_instance

def Decimal (digits : String) (n : Nat) : Prop :=
  digits.toList ≠ [] ∧
  digits.toList.all (fun c => '0' ≤ c && c ≤ '9') = true ∧
  (digits.toList.head? ≠ some '0' ∨ digits = "0") ∧
  digits.toList.foldl (fun a c => 10*a+(c.toNat-'0'.toNat)) 0 = n ∧ n < 2^63

instance (digits : String) (n : Nat) : Decidable (Decimal digits n) := by
  unfold Decimal
  infer_instance

def TypeName (name : String) : Prop := name ∈ ["uint64_t", "uint64_t*", "int"]
def BinarySymbol (op : String) : Prop := op ∈ ["+", "-", "*", "/", "<", ">", "<=", "==", "!=", "="]
def UnarySymbol (op : String) : Prop := op ∈ ["++", "--", "&"]

def lvalue : Expr → Bool
  | .var _ | .index .. => true
  | _ => false

/-- Character-level separators, with no dependence on a printer. -/
inductive Separated {α : Type} (sep : String) (P : String → α → Prop) :
    String → List α → Prop where
  | nil : Separated sep P "" []
  | singleton {s x} : P s x → Separated sep P s [x]
  | cons {s x t xs} : P s x → Separated sep P t xs → xs ≠ [] →
      Separated sep P (s++sep++t) (x::xs)

/-- Each production is a C primary/postfix expression or an explicitly
parenthesized expression; implicit binary precedence is never guessed. -/
inductive Expression : String → Expr → Prop where
  | natural {digits n} : Decimal digits n → Expression digits (.nat n)
  | variable {name} : Identifier name → Expression name (.var name)
  | unary {op text e} : UnarySymbol op → lvalue e = true → Expression text e →
      Expression ("("++op++text++")") (.unary op e)
  | binary {op a b left right} : BinarySymbol op →
      (op = "=" → lvalue left = true) → Expression a left → Expression b right →
      Expression ("("++a++op++b++")") (.binary op left right)
  | index {name text e} : Identifier name → Expression text e →
      Expression ("("++name++"["++text++"])") (.index (.var name) e)
  | call {name text args} : Identifier name → Separated "," Expression text args →
      Expression (name++"("++text++")") (.call (.var name) args)

inductive Declaration : String → Decl → Prop where
  | uninitialized {ty name} : TypeName ty → BindingName name →
      Declaration (ty++" "++name) ⟨ty,name,none⟩
  | initialized {ty name text e} : TypeName ty → BindingName name → Expression text e →
      Declaration (ty++" "++name++"="++text) ⟨ty,name,some e⟩

inductive Condition : String → Option Expr → Prop where
  | omitted : Condition "" none
  | present {text e} : Expression text e → Condition text (some e)

mutual
  /-- Matched statements: every if has its own explicit else. A declaration
  is a block item or a for initializer, not a C11 controlled statement. -/
  inductive Statement : String → Stmt → Prop where
    | skip : Statement ";" .skip
    | block {text body} : Separated "\n" BlockItem text body →
        Statement ("{"++text++"}") (.sequence body)
    | evaluate {text e} : Expression text e → Statement (text++";") (.eval e)
    | returnValue {text e} : Expression text e → Statement ("return "++text++";") (.returnStmt e)
    | branch {c yes no e a b} : Expression c e → Statement yes a → Statement no b →
        Statement ("if("++c++")"++yes++"else "++no) (.branch e a b)
    | whileLoop {c body e b} : Expression c e → Statement body b →
        Statement ("while("++c++")"++body) (.whileLoop e b)
    | forLoop {init c step body d condition increment b} : Declaration init d →
        Condition c condition → Expression step increment → Statement body b →
        Statement ("for("++init++";"++c++";"++step++")"++body)
          (.forLoop (.declare [d]) condition increment b)

  inductive BlockItem : String → Stmt → Prop where
    | statement {text s} : Statement text s → BlockItem text s
    | declaration {text d} : Declaration text d → BlockItem (text++";") (.declare [d])
end

inductive Parameter : String → String × String → Prop where
  | typed {ty name} : TypeName ty → BindingName name → Parameter (ty++" "++name) (ty,name)

inductive FunctionSyntax : String → Function → Prop where
  | definition {ty name params body ptext btext items} : TypeName ty → BindingName name →
      Separated "," Parameter ptext params → Statement btext (.sequence items) →
      body = .sequence items →
      FunctionSyntax (ty++" "++name++"("++ptext++")"++btext++"\n") ⟨ty,name,params,body⟩

/-- Phase1/2-safe comment characters: ASCII, no trigraph question marks or
line-splicing backslashes. The literal terminator is excluded independently. -/
def commentChar (c : Char) : Bool := c == '\n' || c == '\t' ||
  (' ' ≤ c && c ≤ '~' && c != '\\' && c != '?')
def CommentBody (s : String) : Prop :=
  s.toList.all commentChar = true ∧ s.contains "*/" = false

inductive Prelude : String → Bool → Prop where
  | counter {comment} : CommentBody comment →
      Prelude ("/*"++comment++"*/\n#include <stdint.h>\n\n") false
  | driver {comment} : CommentBody comment →
      Prelude ("/*"++comment++"*/\n#include <stdint.h>\n#include <stdio.h>\n\n") true

inductive CounterProgram : String → List Function → Prop where
  | translationUnit {pre text fs} : Prelude pre false → Separated "\n" FunctionSyntax text fs →
      fs ≠ [] → CounterProgram (pre++text) fs

open RamanujanPV.QuotientDriverSource

inductive PrototypeSyntax : String → Prototype → Prop where
  | external {ty name params text} : TypeName ty → BindingName name →
      Separated "," Parameter text params →
      PrototypeSyntax ("extern "++ty++" "++name++"("++text++");\n") ⟨ty,name,params⟩

inductive ArraySyntax : String → StaticArray → Prop where
  | u64 {name count digits} : BindingName name → Decimal digits count → 0 < count →
      ArraySyntax ("static uint64_t "++name++"["++digits++"];\n") ⟨name,.uint64,count⟩

inductive GlobalsSyntax : String → List StaticArray → Prop where
  | nil : GlobalsSyntax "" []
  | cons {s a rest xs} : ArraySyntax s a → GlobalsSyntax rest xs →
      GlobalsSyntax (s++rest) (a::xs)

inductive DriverProgram : String → TranslationUnit → Prop where
  | translationUnit {pre proto globals main p g f} : Prelude pre true →
      PrototypeSyntax proto p → GlobalsSyntax globals g → FunctionSyntax main f →
      f.returnType = "int" → f.name = "main" → f.parameters = [] →
      DriverProgram (pre++proto++globals++"\n"++main) ⟨p,g,f⟩

end RHOcticPush.CounterSyntax
