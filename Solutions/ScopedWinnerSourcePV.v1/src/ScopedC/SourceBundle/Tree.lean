/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import ScopedC.CData
import ScopedC.Header

namespace ScopedC.SourceBundle
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- The pathname and the exact file text. The bundle association gate checks
 that the include_str source and compiler input refer to this same owned file. -/
structure File where
  name : String
  text : String

def directive (name : String) : String := "#include \""++name++"\"\n"

/-- A finite preprocessor tree. Its semantic values are never obtained by
 evaluating the concatenation of the complete source translation unit. -/
inductive Tree (α : Type) where
  | leaf (file : File) (value : α)
  | pair (file : File) (left right : Tree α)

def Tree.file {α : Type} : Tree α → File
  | .leaf f _ | .pair f _ _ => f

def Tree.values {α : Type} : Tree α → List α
  | .leaf _ v => [v]
  | .pair _ a b => a.values ++ b.values

def Tree.files {α : Type} : Tree α → List File
  | .leaf f _ => [f]
  | .pair f a b => f :: (a.files ++ b.files)

/-- Structural source binding for a tiny exact-include subset. The generic
 pinned compiler/preprocessor expands these ordinary quoted includes. Every
 application leaf separately proves its actual syntax; no program output or
 whole application correctness is an external leaf. -/
inductive Tree.Bound {α : Type} (Leaf : α → File → Prop) : Tree α → Prop
  | leaf {f v} (exact : Leaf v f) : Bound Leaf (.leaf f v)
  | pair {f a b} (left : Bound Leaf a) (right : Bound Leaf b)
      (exact : f.text = directive a.file.name ++ directive b.file.name) :
      Bound Leaf (.pair f a b)

/-- A generic include-expansion contract over an actual file loader. This is
 a mathematical specification of the disclosed pinned preprocessor boundary,
 not a claim to have verified Clang's implementation. -/
inductive Expands {α : Type} (load : String → Option String)
    (Leaf : α → File → Prop) : String → List α → Prop
  | leaf {f : File} {v : α} (read : load f.name = some f.text) (bound : Leaf v f) : Expands load Leaf f.name [v]
  | pair {f : File} {a b : String} {x y : List α} (read : load f.name = some f.text)
      (exact : f.text = directive a ++ directive b)
      (left : Expands load Leaf a x) (right : Expands load Leaf b y) :
      Expands load Leaf f.name (x++y)

 theorem Tree.expands {α : Type} {Leaf : α → File → Prop} {t : Tree α}
    (bound : t.Bound Leaf) (load : String → Option String)
    (same_files : ∀ f ∈ t.files, load f.name = some f.text) :
    Expands load Leaf t.file.name t.values := by
  induction bound with
  | leaf h => exact Expands.leaf (same_files _ (by simp [Tree.files,Tree.file])) h
  | pair left right exact ihl ihr =>
    apply Expands.pair (same_files _ (by simp [Tree.files,Tree.file])) exact
    · apply ihl
      intro f hf
      exact same_files f (by simp [Tree.files,hf])
    · apply ihr
      intro f hf
      exact same_files f (by simp [Tree.files,hf])

/-- A nonempty initializer fragment. Prefix commas separate independent
 include leaves without trailing-comma or token-boundary changes. -/
structure Fragment where
  prefixComma : Bool
  elements : List Expr

def renderFragment (f : Fragment) : Option String := do
  let body ← f.elements.mapM (renderExpr 1000)
  pure ((if f.prefixComma then "," else "") ++ String.intercalate "," body ++ "\n")

def FragmentsFollow : List Fragment → Prop
  | [] => False
  | first::rest => first.prefixComma = false ∧ first.elements ≠ [] ∧
      ∀ f ∈ rest, f.prefixComma = true ∧ f.elements ≠ []

def arrayText (type name : String) (count : Nat) (body : String) : String :=
  type++" "++name++"["++toString count++"]={\n"++directive body++"};\n"

def ArrayBound (d : Decl) (file : File) : Prop :=
  ∃ body : Tree Fragment,
    body.Bound (fun f file => renderFragment f = some file.text) ∧
    FragmentsFollow body.values ∧
    d = ({type:=d.type,name:=d.name,value:=some (.record (body.values.flatMap Fragment.elements)),arrayExtent:=some (body.values.flatMap Fragment.elements).length} : Decl) ∧
    file.text = arrayText d.type d.name (body.values.flatMap Fragment.elements).length body.file.name

inductive Piece where
  | prelude
  | typeDecl (d : Header.TypeDecl)
  | global (d : Decl)
  | array (d : Decl)
  | function (f : Function)

def Piece.functions : Piece → List Function
  | .function f => [f]
  | _ => []
def Piece.globals : Piece → List Decl
  | .global d | .array d => [d]
  | _ => []
def Piece.types : Piece → List Header.TypeDecl
  | .typeDecl d => [d]
  | _ => []

inductive Piece.Bound : Piece → File → Prop
  | prelude {f : File} (exact : f.text = Header.externalPrelude) : Bound .prelude f
  | typeDecl {d : Header.TypeDecl} {f : File} (exact : Header.renderTypeDecl d = f.text) : Bound (.typeDecl d) f
  | global {d : Decl} {f : File} (exact : (do pure ("static "++(←renderDecl d)++";\n")) = some f.text) : Bound (.global d) f
  | array {d : Decl} {f : File} (exact : ArrayBound d f) : Bound (.array d) f
  | function {d : Function} {f : File} (exact : renderFunction d = some f.text) : Bound (.function d) f

end ScopedC.SourceBundle
