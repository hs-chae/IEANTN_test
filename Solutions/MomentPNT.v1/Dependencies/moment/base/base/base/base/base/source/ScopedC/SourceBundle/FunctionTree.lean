/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.SourceBundle.Tree

namespace ScopedC.SourceBundle.FunctionTree
open ScopedC.Syntax
set_option autoImplicit false
set_option maxHeartbeats 0

/-- A genuine source statement, not a mathematical result or an application
execution oracle. The selected parenthesized C subset and the preprocessor
boundary are exactly those of the existing source bundle. -/
structure StatementFragment where
  statement : Stmt

def renderFragment (fragment : StatementFragment) : Option String := do
  pure ((←renderStmt 1000 fragment.statement)++"\n")

def LeafBound (fragment : StatementFragment) (file : File) : Prop :=
  renderFragment fragment = some file.text

def signature (f : Function) : String :=
  f.returnType++" "++f.name++"("++Syntax.join (f.parameters.map (fun(t,n)=>t++" "++n))++")"

def wrapperText (f : Function) (bodyName : String) : String :=
  signature f++"{\n"++directive bodyName++"}\n"

/-- Source grammar for a function whose block is physically assembled from
verified short statements. This avoids evaluating a giant closed String join.
It preserves the exact existing Function AST consumed by SourceCalls.

The actual build association must account for `file :: body.files`, not just
the outer wrapper. `expands` states this requirement over the real file loader.
No constructor mentions an expected numerical output or successful program. -/
structure Bound (f : Function) (file : File) (body : Tree StatementFragment) : Prop where
  statements : body.Bound LeafBound
  shape : f.body = .sequence (body.values.map StatementFragment.statement)
  exact : file.text = wrapperText f body.file.name

/-- Generic preprocessor/function-block grammar, under the same disclosed
pinned preprocessor contract as SourceBundle.Expands. Each source statement
must be read from its actual bound file; no absent inner file is assumed. -/
inductive Expands (load : String → Option String) : String → Function → Prop
  | block {f : Function} {file : File} {bodyName : String} {fragments : List StatementFragment}
      (read : load file.name = some file.text)
      (exact : file.text = wrapperText f bodyName)
      (statements : SourceBundle.Expands load LeafBound bodyName fragments)
      (shape : f.body = .sequence (fragments.map StatementFragment.statement)) :
      Expands load file.name f

theorem Bound.expands {f : Function} {file : File} {body : Tree StatementFragment}
    (bound : Bound f file body) (load : String → Option String)
    (same_wrapper : load file.name = some file.text)
    (same_body_files : ∀ source ∈ body.files, load source.name = some source.text) :
    Expands load file.name f :=
  .block same_wrapper bound.exact (body.expands bound.statements load same_body_files) bound.shape

theorem Bound.expands_from_all_files {f : Function} {file : File} {body : Tree StatementFragment}
    (bound : Bound f file body) (load : String → Option String)
    (same_files : ∀ source ∈ file::body.files, load source.name = some source.text) :
    Expands load file.name f := by
  apply bound.expands load
  · exact same_files file List.mem_cons_self
  · intro source member
    exact same_files source (List.mem_cons_of_mem file member)

end ScopedC.SourceBundle.FunctionTree
