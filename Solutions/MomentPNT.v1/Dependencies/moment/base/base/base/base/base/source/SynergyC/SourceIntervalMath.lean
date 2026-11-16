/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.CeilDivMath
import SynergyC.IntervalAddBody
import SynergyBasis.BoxRealSound

namespace SynergyC.SourceIntervalMath
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls
open SynergyC.Word512 SynergyC.WordFrames SynergyC.ZeroBody
open ScopedNumerical SynergyBasis
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem ceiling_matches_model {a b : Int} (hb : 0 < b) :
    CeilDivBody.result a b = ProofBox.ceilDiv a b := by
  unfold CeilDivBody.result bit ProofBox.ceilDiv ProofBox.floorDiv
  rw [if_pos hb,Int.neg_ediv]
  have hs : Int.sign b = 1 := Int.sign_eq_one_of_pos hb
  rw [hs]
  by_cases hd : b ∣ a <;> simp [hd] <;> ring

/-- Actual source ceiling division produces the mathematical directed-rounding
operation, rather than independently checking a supplied output certificate. -/
theorem source_ceiling (code : List Function) (installed : Generated.f_ceilDiv ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (checked : CeilDivBody.addParameters code = true)
    {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hb0 : 0 < b) :
    SourceCall Header.layout code 2 "ceilDiv" [value a,value b] s
      (value (ProofBox.ceilDiv a b)) s := by
  rw [←ceiling_matches_model hb0]
  exact CeilDivBody.source_ceilDiv_total code installed addInstalled checked ctx ha hb hb0

def represented (a : ProofBox) : Value := interval a.lo a.hi
def representable (a : ProofBox) : Prop := Range a.lo ∧ Range a.hi

theorem source_add (code : List Function) (installed : Generated.f_add ∈ code)
    (addInstalled : Generated.f_addU ∈ code) {s : State} (ctx : MaxContext s)
    {a b : ProofBox} (ha : representable a) (hb : representable b)
    (hs : representable (ProofBox.add a b)) :
    SourceCall Header.layout code 2 "add" [represented a,represented b] s
      (represented (ProofBox.add a b)) s :=
  IntervalAddBody.source_add code installed addInstalled ctx ha.1 ha.2 hb.1 hb.2 hs.1 hs.2

theorem source_add_enclosure (code : List Function) (installed : Generated.f_add ∈ code)
    (addInstalled : Generated.f_addU ∈ code) {s : State} (ctx : MaxContext s)
    {a b : ProofBox} {x y : ℝ} (ha : representable a) (hb : representable b)
    (hs : representable (ProofBox.add a b))
    (hx : RealBox.Contains 128 a x) (hy : RealBox.Contains 128 b y) :
    SourceCall Header.layout code 2 "add" [represented a,represented b] s
      (represented (ProofBox.add a b)) s ∧ RealBox.Contains 128 (ProofBox.add a b) (x+y) :=
  ⟨source_add code installed addInstalled ctx ha hb hs,RealBox.add_sound hx hy⟩

end SynergyC.SourceIntervalMath
