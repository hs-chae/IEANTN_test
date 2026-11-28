import Init

set_option autoImplicit false

namespace RH080Next.PrivateTopShape
universe u

/-- Ten symbolic append boundaries only; no numerical list is inspected. -/
theorem consAppend10 {α : Type u} (h : α)
    (t r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : List α) :
    (((((((((((h :: t) ++ r0) ++ r1) ++ r2) ++ r3) ++ r4) ++ r5) ++ r6) ++ r7) ++ r8) ++ r9) =
      h :: ((((((((((t ++ r0) ++ r1) ++ r2) ++ r3) ++ r4) ++ r5) ++ r6) ++ r7) ++ r8) ++ r9) := by
  rfl

/-- Direct specialization of the existing generic library homomorphism theorem. -/
theorem appendFold_cons {α : Type u} (h : α) (t : List α) (rs : List (List α)) :
    rs.foldl (fun left right => left ++ right) (h :: t) =
      h :: rs.foldl (fun left right => left ++ right) t :=
  List.foldl_hom (List.cons h) (fun _ _ => List.cons_append)

#print axioms consAppend10
#print axioms appendFold_cons
end RH080Next.PrivateTopShape
