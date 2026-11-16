import SynergyAnalytic.HeightPointConstants
import OriginalScalarSemantics
namespace SynergyAnalytic.HeightPoint
open ScopedNumerical ScopedNumerical.ProofBox SynergyBasis SynergyBasis.Positive
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def hValue : ProofBox := ⟨9776187655687010469267555977101839261184,9776187655687010469267555977101839268028⟩
theorem kernel_h : BoxModel.logPos 384 (literal p 3000000000000 1)=some hValue := by decide +kernel
theorem h_sound : RealBox.Contains p hValue (Real.log WinnerOriginalScalars.height) := by
  exact BoxModel.logPos_sound 384 (by simpa [WinnerOriginalScalars.height] using RealBox.literal_sound p 3000000000000 1 (by decide)) kernel_h
def n : Nat := 2048
def logGrid (i : Nat) : ProofBox := add hValue (mul p (sub (literal p 60 1) hValue) (mul p (literal p i n) (literal p i n)))
noncomputable def realLogGrid (i : Nat) : ℝ := Real.log WinnerOriginalScalars.height+(60-Real.log WinnerOriginalScalars.height)*((i:ℝ)/n)^2
noncomputable def realGrid (i : Nat) : ℝ := Real.exp (realLogGrid i)
theorem logGrid_sound (i : Nat) : RealBox.Contains p (logGrid i) (realLogGrid i) := by
  have h60 := RealBox.literal_sound p 60 1 (by decide)
  have hi := RealBox.literal_sound p (i:Int) n (by norm_num [n])
  have hh := RealBox.add_sound h_sound (RealBox.mul_sound (RealBox.sub_sound h60 h_sound) (RealBox.mul_sound hi hi))
  simpa only [logGrid,realLogGrid,div_one,Nat.cast_one,Int.cast_ofNat,Int.cast_natCast,←pow_two] using hh
#print axioms h_sound
#print axioms logGrid_sound
end SynergyAnalytic.HeightPoint
