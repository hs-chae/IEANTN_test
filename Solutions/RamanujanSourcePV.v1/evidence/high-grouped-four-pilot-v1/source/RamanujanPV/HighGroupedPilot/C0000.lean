/- Copyright (c) 2026 IEANTN contributors. Apache 2.0. -/
import RamanujanPV.HighTransitionCount.Data
namespace RamanujanPV.HighGroupedPilot.C0000
open QuotientDemandCheck HighTransitionCount
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
private theorem and_assoc_pure (a b c : Bool) : ((a&&b)&&c)=(a&&(b&&c)) := by
  cases a <;> cases b <;> cases c <;> rfl
/-- Pure Boolean concatenation; explicit equality composition avoids propext. -/
theorem append (check : Nat→Bool) (n m : Nat) :
    ∀i, allFrom check i (n+m)=(allFrom check i n &&allFrom check (i+n) m) := by
  induction n with
  | zero =>
    intro i
    rw [Nat.zero_add,Nat.add_zero]
    rfl
  | succ n ih =>
    intro i
    rw [Nat.succ_add]
    change (check i && allFrom check (i+1) (n+m)) =
      ((check i && allFrom check (i+1) n) && allFrom check (i+(n+1)) m)
    have address : (i+1)+n=i+(n+1) :=
      (Nat.add_assoc i 1 n).trans (congrArg (Nat.add i) (Nat.add_comm 1 n))
    exact (congrArg (fun b => check i && b) (ih (i+1))).trans
      ((and_assoc_pure (check i) (allFrom check (i+1) n)
        (allFrom check ((i+1)+n) m)).symm.trans
          (congrArg (fun b => (check i && allFrom check (i+1) n) && b)
            (congrArg (fun j => allFrom check j m) address)))
theorem append_checked {check : Nat→Bool} {i n m : Nat}
    (left : allFrom check i n=true) (right : allFrom check (i+n) m=true) :
    allFrom check i (n+m)=true := by
  have h:=append check n m i
  rw [left,right] at h
  exact h

theorem sub_0 : allFrom (checkEntry nodes gaps gapCount) 0 4096=true := by decide +kernel
theorem sub_1 : allFrom (checkEntry nodes gaps gapCount) 4096 4096=true := by decide +kernel
theorem sub_2 : allFrom (checkEntry nodes gaps gapCount) 8192 4096=true := by decide +kernel
theorem sub_3 : allFrom (checkEntry nodes gaps gapCount) 12288 4096=true := by decide +kernel
theorem sub_4 : allFrom (checkEntry nodes gaps gapCount) 16384 4096=true := by decide +kernel
theorem sub_5 : allFrom (checkEntry nodes gaps gapCount) 20480 4096=true := by decide +kernel
theorem sub_6 : allFrom (checkEntry nodes gaps gapCount) 24576 4096=true := by decide +kernel
theorem sub_7 : allFrom (checkEntry nodes gaps gapCount) 28672 4096=true := by decide +kernel
theorem part_grouped : allFrom (checkEntry nodes gaps gapCount) 0 32768=true := by
  have tail6 : allFrom (checkEntry nodes gaps gapCount) 24576 8192=true := append_checked (n:=4096) (m:=4096) sub_6 sub_7
  have tail5 : allFrom (checkEntry nodes gaps gapCount) 20480 12288=true := append_checked (n:=4096) (m:=8192) sub_5 tail6
  have tail4 : allFrom (checkEntry nodes gaps gapCount) 16384 16384=true := append_checked (n:=4096) (m:=12288) sub_4 tail5
  have tail3 : allFrom (checkEntry nodes gaps gapCount) 12288 20480=true := append_checked (n:=4096) (m:=16384) sub_3 tail4
  have tail2 : allFrom (checkEntry nodes gaps gapCount) 8192 24576=true := append_checked (n:=4096) (m:=20480) sub_2 tail3
  have tail1 : allFrom (checkEntry nodes gaps gapCount) 4096 28672=true := append_checked (n:=4096) (m:=24576) sub_1 tail2
  have tail0 : allFrom (checkEntry nodes gaps gapCount) 0 32768=true := append_checked (n:=4096) (m:=28672) sub_0 tail1
  exact tail0
example : allFrom (checkEntry nodes gaps gapCount) 0 32768=true := part_grouped
#check part_grouped
#print axioms append
#print axioms append_checked
#print axioms sub_0
#print axioms sub_1
#print axioms sub_2
#print axioms sub_3
#print axioms sub_4
#print axioms sub_5
#print axioms sub_6
#print axioms sub_7
#print axioms part_grouped
end RamanujanPV.HighGroupedPilot.C0000
