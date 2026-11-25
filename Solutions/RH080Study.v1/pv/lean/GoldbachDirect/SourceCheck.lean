import GoldbachDirect.Syntax
import GoldbachDirect.Correspondence.Lexical
import Mathlib.Tactic.Basic

namespace GoldbachDirect

private def quoted (quote : Char) : Nat → List Char → List Char → Option (String × List Char)
  | 0,_,_ => none
  | _+1,[],_ => none
  | fuel+1,c::cs,acc =>
    if c = quote then some (String.ofList ((c::acc).reverse),cs)
    else if c = '\\' then
      match cs with
      | [] => none
      | d::ds => quoted quote fuel ds (d::c::acc)
    else if c = '\n' then none else quoted quote fuel cs (c::acc)

private def blockComment : Nat → List Char → Option (List Char)
  | 0,_ => none
  | _+1,[] => none
  | _+1,'*'::'/'::rest => some rest
  | fuel+1,_::rest => blockComment fuel rest

private def lexAux : Nat → List Char → Option (List String)
  | 0,[] => some []
  | 0,_::_ => none
  | _+1,[] => some []
  | fuel+1,'/'::'/'::rest => lexAux fuel (rest.dropWhile (· != '\n'))
  | fuel+1,'/'::'*'::rest => do lexAux fuel (← blockComment (rest.length+1) rest)
  | fuel+1,c::rest => do
    if c.isWhitespace then lexAux fuel rest
    else if c = '"' || c = '\'' then
      let (token,tail) ← quoted c (rest.length+1) rest [c]
      return token :: (← lexAux fuel tail)
    else if c.isAlphanum || c = '_' then
      let word := rest.takeWhile (fun x => x.isAlphanum || x = '_')
      let tail := rest.dropWhile (fun x => x.isAlphanum || x = '_')
      return String.ofList (c::word) :: (← lexAux fuel tail)
    else
      let three := String.ofList ((c::rest).take 3)
      let two := String.ofList ((c::rest).take 2)
      if three ∈ ["<<<",">>>","<<=",">>="] then
        return three :: (← lexAux fuel ((c::rest).drop 3))
      else if two ∈ ["==","!=","<=",">=","&&","||","<<",">>","->","+=","-=","*=","/=","%=","&=","|=","^=","++","--"] then
        return two :: (← lexAux fuel ((c::rest).drop 2))
      else if c ∈ ['#','(',')','[',']','{','}',';',':',',','.','?','+','-','*','/','%','<','>','=','!','~','&','|','^'] then
        return String.singleton c :: (← lexAux fuel rest)
      else none

/-- Raw supported lexical tokens, rejecting unknown characters and unterminated
literals/comments. Physical-source translation restrictions and independent
syntax correspondence are established by acceptedSource, not by this lexer alone. -/
def tokenize (source : String) : Option (List String) := lexAux (source.length+1) source.toList

def CType.tokens : CType → List String
  | .void => ["void"] | .boolean => ["bool"] | .char => ["char"]
  | .u8 => ["uint8_t"] | .u32 => ["uint32_t"] | .u64 => ["uint64_t"]
  | .i32 => ["int32_t"] | .size => ["size_t"]
  | .int => ["int"] | .ull => ["unsigned","long","long"]
  | .cudaStream => ["cudaStream_t"] | .cudaError => ["cudaError_t"] | .file => ["FILE"]
  | .pointer t => t.tokens ++ ["*"]
  | .const t => "const" :: t.tokens

def Unary.token : Unary → String
  | .logicalNot => "!" | .bitNot => "~" | .negate => "-"
  | .address => "&" | .dereference => "*"

def Binary.token : Binary → String
  | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .mod => "%"
  | .shl => "<<" | .shr => ">>" | .bitAnd => "&" | .bitOr => "|" | .bitXor => "^"
  | .eq => "==" | .ne => "!=" | .lt => "<" | .le => "<=" | .gt => ">" | .ge => ">="
  | .logicalAnd => "&&" | .logicalOr => "||"

private def escape (c : Char) : String :=
  if c = '\n' then "\\n" else if c = '\r' then "\\r" else if c = '\t' then "\\t"
  else if c = '\\' then "\\\\" else if c = '"' then "\\\"" else String.singleton c

def Literal.tokens : Literal → List String
  | .integer value suffix => [toString value ++ suffix]
  | .boolean true => ["true"] | .boolean false => ["false"]
  | .nullPointer => ["NULL"]
  | .string value => ["\"" ++ String.join (value.toList.map escape) ++ "\""]
  | .character value => ["'" ++ (if value = '\'' then "\\'" else escape value) ++ "'"]

def comma (items : List (List String)) : List String := List.flatten (items.intersperse [","])

def Expr.tokens : Expr → List String
  | .literal value => value.tokens
  | .paren value => "(" :: value.tokens ++ [")"]
  | .variable name => [name]
  | .cast type value => ["("] ++ type.tokens ++ [")"] ++ value.tokens
  | .unary op value => op.token :: value.tokens
  | .binary op left right => left.tokens ++ [op.token] ++ right.tokens
  | .index base offset => base.tokens ++ ["["] ++ offset.tokens ++ ["]"]
  | .member base field arrow => base.tokens ++ [if arrow then "->" else ".",field]
  | .call name args => [name,"("] ++ comma (args.map Expr.tokens) ++ [")"]
  | .conditional test yes no => test.tokens ++ ["?"] ++ yes.tokens ++ [":"] ++ no.tokens

def Stmt.tokens : Stmt → List String
  | .block body => ["{"] ++ List.flatten (body.map Stmt.tokens) ++ ["}"]
  | .declare type name value => type.tokens ++ [name] ++ (match value with
      | none => [] | some value => ["="] ++ value.tokens) ++ [";"]
  | .assign destination value => destination.tokens ++ ["="] ++ value.tokens ++ [";"]
  | .assignOp op destination value => destination.tokens ++ [op.token ++ "="] ++ value.tokens ++ [";"]
  | .expression value => value.tokens ++ [";"]
  | .ite condition yes no => ["if","("] ++ condition.tokens ++ [")"] ++ yes.tokens ++
      (match no with | none => [] | some body => ["else"] ++ body.tokens)
  | .whileLoop condition body => ["while","("] ++ condition.tokens ++ [")"] ++ body.tokens
  | .forLoop initial condition advance body => ["for","("] ++ initial.tokens ++ condition.tokens ++
      [";"] ++ advance.tokens.dropLast ++ [")"] ++ body.tokens
  | .returnValue value => ["return"] ++ (match value with | none => [] | some e => e.tokens) ++ [";"]
  | .breakLoop => ["break",";"] | .continueLoop => ["continue",";"]
  | .label name => [name,":"] | .gotoLabel name => ["goto",name,";"]
  | .launch name grid blockSize shared stream args => [name,"<<<"] ++
      comma [grid.tokens,blockSize.tokens,shared.tokens,stream.tokens] ++ [">>>","("] ++
      comma (args.map Expr.tokens) ++ [")",";"]

def Qualifier.token : Qualifier → String
  | .static => "static" | .inline => "inline" | .host => "__host__"
  | .device => "__device__" | .global => "__global__"

def Function.tokens (f : Function) : List String :=
  f.qualifiers.map Qualifier.token ++ f.result.tokens ++ [f.name,"("] ++
    (if f.emptyVoid && f.parameters.isEmpty then ["void"] else
      comma (f.parameters.map (fun (type,name) => type.tokens ++ [name]))) ++ [")"] ++ f.body.tokens

def Header.tokens : Header → List String
  | .stdint => ["<","stdint",".","h",">"]
  | .stddef => ["<","stddef",".","h",">"]
  | .stdbool => ["<","stdbool",".","h",">"]
  | .stdlib => ["<","stdlib",".","h",">"]
  | .stdio => ["<","stdio",".","h",">"]
  | .inttypes => ["<","inttypes",".","h",">"]
  | .cudaRuntime => ["<","cuda_runtime",".","h",">"]
  | .primes => ["\"primes.h\""] | .kernels => ["\"kernels.cuh\""]

def Top.tokens : Top → List String
  | .include header => ["#","include"] ++ header.tokens
  | .pragmaOnce => ["#","pragma","once"]
  | .function f => f.tokens

def Program.tokens (program : Program) : List String := List.flatten (program.map Top.tokens)

/-- Shape guard for the supported unambiguous expression grammar. Binary
subexpressions must be explicitly grouped, avoiding a manually misassociated AST. -/
def Expr.atomic : Expr → Bool
  | .binary .. | .conditional .. => false
  | _ => true

private def groupedAux : Nat → Expr → Bool
  | 0,_ => false
  | _+1,.literal _ | _+1,.variable _ => true
  | fuel+1,.paren e => groupedAux fuel e
  | fuel+1,.cast _ e | fuel+1,.unary _ e => e.atomic && groupedAux fuel e
  | fuel+1,.binary _ a b => a.atomic && b.atomic && groupedAux fuel a && groupedAux fuel b
  | fuel+1,.index a b => a.atomic && groupedAux fuel a && groupedAux fuel b
  | fuel+1,.member a _ _ => a.atomic && groupedAux fuel a
  | fuel+1,.call _ args => args.all (groupedAux fuel)
  | fuel+1,.conditional a b c => a.atomic && b.atomic && c.atomic &&
      groupedAux fuel a && groupedAux fuel b && groupedAux fuel c

def Expr.grouped (e : Expr) : Bool := groupedAux 1024 e

/-- Syntax identity only; semantic use additionally requires the supported
program's well-typed/source-legal execution relation, never a source hash premise. -/
def checkedSource (source : String) (program : Program) : Bool :=
  tokenize source == some program.tokens

theorem checkedSource_tokens {source : String} {program : Program}
    (checked : checkedSource source program = true) : tokenize source = some program.tokens := by
  simpa only [checkedSource,beq_iff_eq] using checked

namespace Lexical

theorem run_takeWhile_dropWhile (p : Char → Bool) (chars : List Char) :
    Run p chars (chars.takeWhile p) (chars.dropWhile p) := by
  induction chars with
  | nil => exact Run.endOfInput
  | cons c cs ih =>
      cases h : p c with
      | false => simpa [h] using (Run.stop h : Run p (c :: cs) [] (c :: cs))
      | true => simpa [h] using (Run.next h ih)

end Lexical

private theorem quoted_sound (fuel : Nat) {quote : Char} {chars acc : List Char}
    {token : String} {tail : List Char} (checked : quoted quote fuel chars acc = some (token, tail)) :
    ∃ body, Lexical.QuotedBody quote chars body tail ∧
      token = String.ofList (acc.reverse ++ body) := by
  induction fuel generalizing chars acc token tail with
  | zero => simp [quoted] at checked
  | succ fuel ih =>
      cases chars with
      | nil => simp [quoted] at checked
      | cons c cs =>
          by_cases close : c = quote
          · simp only [quoted, close, ite_true, Option.some.injEq, Prod.mk.injEq] at checked
            rcases checked with ⟨rfl, rfl⟩
            subst c
            exact ⟨[quote], .close, by simp [List.reverse_cons]⟩
          · by_cases escape : c = '\\'
            · subst c
              cases cs with
              | nil => simp [quoted, close] at checked
              | cons d ds =>
                  simp only [quoted, close, ite_false, ite_true] at checked
                  obtain ⟨body, rel, eq⟩ := ih checked
                  refine ⟨'\\' :: d :: body, .escape close rel, ?_⟩
                  simpa [List.reverse_cons, List.append_assoc] using eq
            · by_cases newline : c = '\n'
              · subst c
                simp [quoted, close] at checked
              · simp only [quoted, close, ite_false, escape, newline] at checked
                obtain ⟨body, rel, eq⟩ := ih checked
                exact ⟨c :: body, .ordinary close escape newline rel,
                  by simpa [List.reverse_cons, List.append_assoc] using eq⟩

private theorem blockComment_sound (fuel : Nat) {chars tail : List Char}
    (checked : blockComment fuel chars = some tail) : Lexical.BlockBody chars tail := by
  induction fuel generalizing chars tail with
  | zero => simp [blockComment] at checked
  | succ fuel ih =>
      cases chars with
      | nil => simp [blockComment] at checked
      | cons c cs =>
          cases cs with
          | nil =>
              have hrec : blockComment fuel [] = some tail := by
                simpa [blockComment] using checked
              exact .next (by simp) (ih hrec)
          | cons d ds =>
              by_cases star : c = '*'
              · subst c
                by_cases slash : d = '/'
                · subst d
                  simp only [blockComment, Option.some.injEq] at checked
                  subst tail
                  exact .close
                · have hrec : blockComment fuel (d :: ds) = some tail := by
                    simpa [blockComment, slash] using checked
                  exact .next (by simp [slash]) (ih hrec)
              · have hrec : blockComment fuel (d :: ds) = some tail := by
                  simpa [blockComment, star] using checked
                exact .next (by simp [star]) (ih hrec)

private theorem lexAux_sound (fuel : Nat) {chars : List Char} {tokens : List String}
    (checked : lexAux fuel chars = some tokens) : Lexical.Lexes chars tokens := by
  induction fuel generalizing chars tokens with
  | zero =>
      cases chars with
      | nil => simp only [lexAux, Option.some.injEq] at checked; subst tokens; exact .done
      | cons c cs => simp [lexAux] at checked
  | succ fuel ih =>
      cases chars with
      | nil => simp only [lexAux, Option.some.injEq] at checked; subst tokens; exact .done
      | cons c cs =>
          unfold lexAux at checked
          split at checked
          · contradiction
          · contradiction
          · contradiction
          · rename_i fuel' rest hf hc
            have hfuel : fuel' = fuel := Nat.succ.inj hf.symm
            subst fuel'
            rw [hc]
            exact .lineComment (Lexical.run_takeWhile_dropWhile _ rest) (ih checked)
          · rename_i fuel' rest hf hc
            have hfuel : fuel' = fuel := Nat.succ.inj hf.symm
            subst fuel'
            rw [hc]
            obtain ⟨tail, hb, ht⟩ := Option.bind_eq_some_iff.mp checked
            exact .blockComment (blockComment_sound _ hb) (ih ht)
          · rename_i fuel' first rest notLine notBlock hf hc
            have hfuel : fuel' = fuel := Nat.succ.inj hf.symm
            subst fuel'
            rw [hc]
            have noComment : ∀ suffix, first :: rest ≠ '/' :: '/' :: suffix ∧
                first :: rest ≠ '/' :: '*' :: suffix := by
              intro suffix
              constructor
              · intro heq
                obtain ⟨hfirst, hrest⟩ := List.cons.inj heq
                exact notLine suffix hfirst hrest
              · intro heq
                obtain ⟨hfirst, hrest⟩ := List.cons.inj heq
                exact notBlock suffix hfirst hrest
            split at checked
            · rename_i white
              exact .whitespace white (ih checked)
            · split at checked
              · rename_i isQuote
                obtain ⟨⟨token, tail⟩, hq, htokens⟩ := Option.bind_eq_some_iff.mp checked
                obtain ⟨suffix, hlex, hcons⟩ := Option.bind_eq_some_iff.mp htokens
                change some (token :: suffix) = some tokens at hcons
                cases Option.some.inj hcons
                obtain ⟨body, rel, heq⟩ := quoted_sound _ hq
                have htoken : token = String.ofList (first :: body) := by
                  simpa using heq
                rw [htoken]
                exact .quoted (by simpa using isQuote) rel (ih hlex)
              · split at checked
                · rename_i isWord
                  obtain ⟨suffix, hlex, hcons⟩ := Option.bind_eq_some_iff.mp checked
                  change some (String.ofList (first :: _) :: suffix) = some tokens at hcons
                  cases Option.some.inj hcons
                  exact .word isWord (Lexical.run_takeWhile_dropWhile _ rest) (ih hlex)
                · dsimp only at checked
                  split at checked
                  · rename_i three
                    obtain ⟨suffix, hlex, hcons⟩ := Option.bind_eq_some_iff.mp checked
                    change some (_ :: suffix) = some tokens at hcons
                    cases Option.some.inj hcons
                    exact .punctuation noComment (.three three) (ih hlex)
                  · rename_i noThree
                    split at checked
                    · rename_i two
                      obtain ⟨suffix, hlex, hcons⟩ := Option.bind_eq_some_iff.mp checked
                      change some (_ :: suffix) = some tokens at hcons
                      cases Option.some.inj hcons
                      exact .punctuation noComment (.two noThree two) (ih hlex)
                    · rename_i noTwo
                      split at checked
                      · rename_i one
                        obtain ⟨suffix, hlex, hcons⟩ := Option.bind_eq_some_iff.mp checked
                        change some (_ :: suffix) = some tokens at hcons
                        cases Option.some.inj hcons
                        exact .punctuation noComment (.one noThree noTwo one) (ih hlex)
                      · contradiction

/-- Kernel-checked soundness for every accepted source, against independent character-level
lexical rules. This is a lexical theorem; C++ preprocessing and grammar legality are separate. -/
theorem tokenize_sound {source : String} {tokens : List String}
    (checked : tokenize source = some tokens) : Lexical.declarativeLex source tokens := by
  exact lexAux_sound (source.length + 1) checked

/-- Accepted source checking gives a full lexical derivation of the printed program tokens. -/
theorem checkedSource_lexes {source : String} {program : Program}
    (checked : checkedSource source program = true) :
    Lexical.declarativeLex source program.tokens := by
  exact tokenize_sound (checkedSource_tokens checked)

end GoldbachDirect
