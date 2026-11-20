/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.PackedSieveProvider
import RamanujanPV.PackedSieveByteControl1000
import RamanujanPV.PackedSieveByteBlock0000
import RamanujanPV.CriticalSourceClosed
namespace RamanujanPV.PackedSieveInstances
open QuotientCCell PackedSieveKernel PackedSieveByteCount PackedSieveByteWidth
open PackedSievePrefix PackedSieveProvider
set_option autoImplicit false
set_option maxHeartbeats 0
attribute [local irreducible] SourceExecution

theorem source_endpoint {lo count baseValue : Nat}
    (base : SourceExecution (lo-1) baseValue)
    (hlo : 2≤lo) (hcount : 0<count) (upper : lo+count-1≤2000000000000)
    (storage : count≤QuotientDriverSource.capacity) :
    SourceExecution (lo+count-1)
      (baseValue+byteCount ((count+7)/8) (primeBits lo count)) := by
  have run := source_provider base hlo hcount upper storage (count-1) (by omega)
  have next : count-1+1=count := by omega
  have bytes : (count-1+8)/8=(count+7)/8 := by omega
  have index : lo+(count-1)=lo+count-1 := by omega
  rw [next,bytes,byteCount_prefix,←byteCount_ceil_width,index] at run
  exact run

theorem source_1000 : SourceExecution 38358838683 1644673264 := by
  have result := source_endpoint (lo:=38358837684) (count:=1000)
    CriticalSourceClosed.p_source (by decide) (by decide) (by decide) (by decide)
  rw [show 38358837684+1000-1=38358838683 by decide,
    show (1000+7)/8=125 by decide, PackedSieveByteControl1000.raw_byte_result] at result
  exact result

theorem source_65536 : SourceExecution 38358903219 1644675896 := by
  have result := source_endpoint (lo:=38358837684) (count:=65536)
    CriticalSourceClosed.p_source (by decide) (by decide) (by decide) (by decide)
  rw [show 38358837684+65536-1=38358903219 by decide,
    show (65536+7)/8=8192 by decide, PackedSieveByteBlock0000.raw_byte_result] at result
  exact result

theorem pi_1000 : Nat.primeCounting 38358838683=1644673264 := source_execution_count source_1000

theorem pi_65536 : Nat.primeCounting 38358903219=1644675896 := source_execution_count source_65536
#print axioms source_endpoint
#print axioms source_1000
#print axioms source_65536
#print axioms pi_1000
#print axioms pi_65536
end RamanujanPV.PackedSieveInstances
