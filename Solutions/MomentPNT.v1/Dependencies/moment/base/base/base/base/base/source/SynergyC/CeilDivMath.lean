/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.CeilDivBody

namespace SynergyC.CeilDivBody
open SynergyC.Word512
open ScopedC ScopedC.Syntax ScopedC.Machine ScopedC.SourceCalls SynergyC.WordFrames
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem result_nonnegative {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    0 ≤ result a b := by
  have hq := Int.ediv_nonneg ha hb.le
  have hbit := (bit_range (a%b != 0)).1
  exact add_nonneg hq hbit

theorem result_le_self {a b : Int} (ha : 0 ≤ a) (hb : 0 < b) :
    result a b ≤ a := by
  have hq := Int.ediv_nonneg ha hb.le
  have hqle := Int.ediv_le_self b ha
  have hr := Int.emod_nonneg a (ne_of_gt hb)
  have hid := Int.emod_add_ediv_mul a b
  unfold result bit
  by_cases hz : a%b = 0
  · simpa [hz] using hqle
  · have hrp : 1 ≤ a%b := by omega
    have hb1 : 1 ≤ b := by omega
    have hp : a/b ≤ a/b*b := by nlinarith
    simp only [bne_iff_ne,ne_eq,hz,not_false_eq_true,↓reduceIte]
    nlinarith

theorem result_range {a b : Int} (ha : Range a) (hb : 0 < b) : Range (result a b) :=
  ⟨result_nonnegative ha.1 hb,lt_of_le_of_lt (result_le_self ha.1 hb) ha.2⟩

/-- The overflow precondition of the internal addU is proved from the input
domain. It is not added as a caller's numerical-correctness assumption. -/
theorem source_ceilDiv_total (code : List Function) (installed : Generated.f_ceilDiv ∈ code)
    (addInstalled : Generated.f_addU ∈ code) (checked : addParameters code = true)
    {s : State} (ctx : MaxContext s) {a b : Int}
    (ha : Range a) (hb : Range b) (hb0 : 0 < b) :
    SourceCall Header.layout code 2 "ceilDiv" [value a,value b] s (value (result a b)) s :=
  source_ceilDiv code installed addInstalled checked ctx ha hb hb0 (result_range ha hb0)

end SynergyC.CeilDivBody
