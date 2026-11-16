import SynergyAnalytic.VectorProgram
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical
set_option autoImplicit false
set_option maxHeartbeats 0

def genericPointCheck (seed:Option ProofBox) (evaluate:ProofBox→Option (List ProofBox))
    (cw dw:Option Int) (mi di:Nat) : Bool := match seed with
  | none => false
  | some t => match evaluate t with
    | none => false
    | some values => match values[mi]?,values[di]?,cw,dw with
      | some c,some D,some cword,some dword => decide (c.hi ≤ cword ∧ D.hi ≤ dword ∧ 0 ≤ dword)
      | _,_,_,_ => false

theorem genericPointCheck_decode {seed:Option ProofBox} {evaluate:ProofBox→Option (List ProofBox)}
    {cw dw:Option Int} {mi di:Nat} (h:genericPointCheck seed evaluate cw dw mi di=true) :
    ∃t values c D cword dword,
      seed=some t ∧ evaluate t=some values ∧ values[mi]?=some c ∧ values[di]?=some D ∧
      cw=some cword ∧ dw=some dword ∧ c.hi ≤ cword ∧ D.hi ≤ dword ∧ 0 ≤ dword := by
  cases ht:seed with
  | none => simp [genericPointCheck,ht] at h
  | some t =>
    cases hv:evaluate t with
    | none => simp [genericPointCheck,ht,hv] at h
    | some vs =>
      cases hc:vs[mi]? with
      | none => simp [genericPointCheck,ht,hv,hc] at h
      | some c =>
        cases hd:vs[di]? with
        | none => simp [genericPointCheck,ht,hv,hc,hd] at h
        | some D =>
          cases hcw:cw with
          | none => simp [genericPointCheck,ht,hv,hc,hd,hcw] at h
          | some cword =>
            cases hdw:dw with
            | none => simp [genericPointCheck,ht,hv,hc,hd,hcw,hdw] at h
            | some dword =>
              simp only [genericPointCheck,ht,hv,hc,hd,hcw,hdw,decide_eq_true_eq] at h
              exact ⟨t,vs,c,D,cword,dword,rfl,hv,hc,hd,rfl,rfl,h⟩

#print axioms genericPointCheck_decode
end SynergyAnalytic.HeightPoint
