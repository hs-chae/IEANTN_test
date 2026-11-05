/- Copyright (c) 2026 IEANTN contributors. Released under Apache2.0. -/
import OldAnalytic
namespace WinnerStrongC4
open Real Set MeasureTheory
set_option maxHeartbeats 0
noncomputable def alpha : ℝ := 2371/20000
noncomputable def moment (b : ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  exp (b*y-2*alpha*exp (2*y))*y^n
noncomputable def kernel (u r rzero y : ℝ) : ℝ :=
  exp (2*y-2*alpha*exp (2*y))*(exp (y/6)*(1+y/u)+rzero)^2*(exp y+r)
noncomputable def expanded (j : ℕ→ℝ) (u r rzero : ℝ) : ℝ :=
  j 0+2/u*j 1+1/u^2*j 2+r*(j 3+2/u*j 4+1/u^2*j 5)+
  2*rzero*(j 6+1/u*j 7+r*(j 8+1/u*j 9))+rzero^2*(j 10+r*j 11)
noncomputable def momentAt (y : ℝ) (i : ℕ) : ℝ :=
  match i with
  | 0 => moment (10/3) 0 y
  | 1 => moment (10/3) 1 y
  | 2 => moment (10/3) 2 y
  | 3 => moment (7/3) 0 y
  | 4 => moment (7/3) 1 y
  | 5 => moment (7/3) 2 y
  | 6 => moment (19/6) 0 y
  | 7 => moment (19/6) 1 y
  | 8 => moment (13/6) 0 y
  | 9 => moment (13/6) 1 y
  | 10 => moment 3 0 y
  | 11 => moment 2 0 y
  | _ => 0

theorem exp_multiple (n : ℕ) (y : ℝ) : exp ((n:ℝ)*(y/6))=exp (y/6)^n := by
  exact exp_nat_mul (y/6) n

theorem kernel_expansion (u r rzero y : ℝ) :
    kernel u r rzero y=expanded (momentAt y) u r rzero := by
  have h20 : exp ((10/3:ℝ)*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^20 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h14 : exp ((7/3:ℝ)*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^14 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h19 : exp ((19/6:ℝ)*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^19 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h13 : exp ((13/6:ℝ)*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^13 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h18 : exp (3*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^18 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h12 : exp (2*y-2*alpha*exp (2*y))=exp (-2*alpha*exp (2*y))*exp (y/6)^12 := by
    rw [sub_eq_add_neg,add_comm,exp_add,←exp_multiple];congr 2 <;> norm_num <;> ring
  have h6 : exp y=exp (y/6)^6 := by rw [←exp_multiple];congr 1;ring
  unfold kernel expanded momentAt moment
  rw [h20,h14,h19,h13,h18,h12,h6]
  simp only [div_pow,one_pow]
  ring_nf

theorem moment_continuous (b : ℝ) (n : ℕ) : Continuous (moment b n) := by unfold moment;fun_prop
@[fun_prop] theorem momentAt_continuous (i : ℕ) : Continuous (fun y=>momentAt y i) := by
  unfold momentAt
  split <;> first | exact moment_continuous _ _ | exact continuous_const

theorem integral_expansion (u r rzero a b : ℝ) :
    (∫y in a..b,kernel u r rzero y)=
      expanded (fun i=>(∫y in a..b,momentAt y i)) u r rzero := by
  simp_rw [kernel_expansion]
  unfold expanded
  have hc (i : ℕ) : IntervalIntegrable (fun y=>momentAt y i) volume a b :=
    (momentAt_continuous i).intervalIntegrable _ _
  repeat' first
    | rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    | rw [intervalIntegral.integral_const_mul]

theorem expanded_mono {j k : ℕ→ℝ} {u r rzero : ℝ}
    (hu : 0<u) (hr : 0≤r) (hz : 0≤rzero) (hjk : ∀i<12,j i≤k i) :
    expanded j u r rzero≤expanded k u r rzero := by
  unfold expanded
  gcongr <;> first |positivity |exact hjk _ (by omega)

theorem expanded_parameters {j : ℕ→ℝ} {u ur r rr z zz : ℝ}
    (hj : ∀i<12,0≤j i) (hu : 0<u) (hur : u≤ur)
    (hr : 0≤r) (hrr : r≤rr) (hz : 0≤z) (hzz : z≤zz) :
    expanded j ur r z≤expanded j u rr zz := by
  have hup : 0<ur := hu.trans_le hur
  have hrec : 1/ur≤1/u := one_div_le_one_div_of_le hu hur
  have hrec2 : 1/ur^2≤1/u^2 := one_div_le_one_div_of_le (by positivity)
    (pow_le_pow_left₀ hu.le hur 2)
  have hrec' : 2/ur≤2/u := div_le_div_of_nonneg_left (by norm_num) hu hur
  have hj0:=hj 0 (by omega)
  have hj1:=hj 1 (by omega)
  have hj2:=hj 2 (by omega)
  have hj3:=hj 3 (by omega)
  have hj4:=hj 4 (by omega)
  have hj5:=hj 5 (by omega)
  have hj6:=hj 6 (by omega)
  have hj7:=hj 7 (by omega)
  have hj8:=hj 8 (by omega)
  have hj9:=hj 9 (by omega)
  have hj10:=hj 10 (by omega)
  have hj11:=hj 11 (by omega)
  have hrrp : 0≤rr := hr.trans hrr
  have hzzp : 0≤zz := hz.trans hzz
  unfold expanded
  gcongr
  all_goals first | exact hj _ (by omega) | exact hrec | exact hrec2 | exact hrec' | positivity

 theorem finite_kernel_lower {j : ℕ→ℝ} {u r z : ℝ}
    (hu : 0<u) (hr : 0≤r) (hz : 0≤z)
    (hj : ∀i<12,j i≤∫y in (-12:ℝ)..3,momentAt y i) :
    expanded j u r z≤∫y in (-12:ℝ)..3,kernel u r z y := by
  rw [integral_expansion]
  exact expanded_mono hu hr hz hj

#print axioms expanded_parameters
#print axioms finite_kernel_lower
#print axioms kernel_expansion
#print axioms integral_expansion
#print axioms expanded_mono
end WinnerStrongC4
