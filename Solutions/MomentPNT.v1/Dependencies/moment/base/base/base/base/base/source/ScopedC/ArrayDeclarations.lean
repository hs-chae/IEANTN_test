/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import ScopedC.SourceCalls

namespace ScopedC.ArrayDeclarations
open ScopedC.Syntax ScopedC.Machine
set_option autoImplicit false
set_option maxHeartbeats 0

/-- Allocate automatic array storage and put its name in scope before any
initializer expression is evaluated. Cells start indeterminate. -/
def allocateArray (st : State) (type name : String) (extent : Nat) : State :=
  {st with
    heap := st.heap ++ [{type:=type,cells:=List.replicate extent none,isArray:=true}]
    env := (name,⟨st.heap.length,0,[]⟩)::st.env}

/-- The C++ braced initializer is sequenced left to right. Each element is
converted and stored before the next expression, so references to earlier
initialized elements and shadowing use the actual new object. This is a
fixed source-memory rule, not an application output or callback. -/
def elements (cfg : Layout) (service : Call) (object : Nat) :
    Nat → List Expr → State → Option State
  | _,[],s => some s
  | index,e::es,s => do
    let (v,t) ← evalExpr cfg service 1000 s e
    let (_,u) ← write cfg t ⟨object,index,[]⟩ true v
    elements cfg service object (index+1) es u

/-- Conservative extension for fully specified automatic integer arrays.
Incomplete brace lists, noninteger arrays and other initializer shapes are
unsupported and fail closed. Legacy scalar/uninitialized-array declarations
use exactly the old evaluator. Extent zero is rejected for a braced array.
No existing Machine declaration or historical execution model is changed. -/
def one (cfg : Layout) (service : Call) (d : Decl) (s : State) : Option State :=
  match d.arrayExtent,d.value with
  | some extent,some (.record es) => do
    let _ ← cfg.integers.lookup (normalizeType d.type)
    if extent = 0 || es.length != extent then none else
      elements cfg service s.heap.length 0 es (allocateArray s d.type d.name extent)
  | some _,some _ => none
  | _,_ => Machine.declarations cfg service [d] s

def declarations (cfg : Layout) (service : Call) (ds : List Decl) (s : State) : Option State :=
  ds.foldlM (fun st d => one cfg service d st) s

/-- The unsupported branch of the old evaluator is the only new case. -/
theorem one_legacy {cfg : Layout} {service : Call} {d : Decl} {s : State}
    (legacy : d.arrayExtent.isNone ∨ d.value.isNone) :
    one cfg service d s = Machine.declarations cfg service [d] s := by
  cases ha : d.arrayExtent <;> cases hv : d.value <;> simp_all [one]

theorem all_legacy {cfg : Layout} {service : Call} {ds : List Decl} {s : State}
    (legacy : ∀ d ∈ ds, d.arrayExtent.isNone ∨ d.value.isNone) :
    declarations cfg service ds s = Machine.declarations cfg service ds s := by
  induction ds generalizing s with
  | nil => rfl
  | cons d ds ih =>
    have hd := one_legacy (cfg:=cfg) (service:=service) (s:=s) (legacy d (by simp))
    have ht : ∀ a ∈ ds, a.arrayExtent.isNone ∨ a.value.isNone :=
      fun a ha => legacy a (by simp [ha])
    change (one cfg service d s).bind (fun t => declarations cfg service ds t) = _
    rw [hd]
    have old_cons : Machine.declarations cfg service (d::ds) s =
        (Machine.declarations cfg service [d] s).bind
          (fun t => Machine.declarations cfg service ds t) := by
      simp [Machine.declarations,List.foldlM_cons]
    rw [old_cons]
    congr 1
    funext t
    exact ih ht

end ScopedC.ArrayDeclarations
