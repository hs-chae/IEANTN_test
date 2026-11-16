/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.UnitBody

namespace SynergyC.ScaleFrames
open ScopedC ScopedC.Syntax ScopedC.Machine
open SynergyC.Word512 SynergyC.UnitBody
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem eval_scale_interval_frame (service : Call) (fuel : Nat) {s : State}
    (ctx : ScaleContext s) (al ah bl bh : Int) :
    evalExpr Header.layout service (fuel+1) (IntervalValues.frame s al ah bl bh) (.var "S") =
      some (value scale,IntervalValues.frame s al ah bl bh) := by
  have get : getVar (IntervalValues.frame s al ah bl bh) "S" = some ctx.address := by
    simp [getVar,IntervalValues.frame,allocate,List.lookup,ctx.located]
  have read : Machine.read Header.layout (IntervalValues.frame s al ah bl bh) ctx.address = some (value scale) := by
    rw [IntervalValues.frame,WordFrames.read_append]
    · rw [WordFrames.read_append]
      · exact ctx.contents
      · exact ctx.allocated
    · simpa [allocate] using Nat.lt.step ctx.allocated
  have heap : (IntervalValues.frame s al ah bl bh).heap[ctx.address.object]? = some ctx.object := by
    simp only [IntervalValues.frame,allocate]
    rw [List.getElem?_append_left (by simpa using Nat.lt.step ctx.allocated)]
    rw [List.getElem?_append_left ctx.allocated]
    exact ctx.heap_entry
  rw [evalExpr]
  simp [get,heap,ctx.scalar,read]

end SynergyC.ScaleFrames
