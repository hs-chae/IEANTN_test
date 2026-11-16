/- Copyright (c) 2026 IEANTN contributors. Apache-2.0. -/
import SynergyC.IntervalMulBody
import SynergyC.IntervalDivBody
import SynergyC.DivNBody
import SynergyC.PositiveSubBody
import SynergyC.RatBody

namespace SynergyC.ComputableIntervalService
open ScopedC ScopedC.Syntax
set_option autoImplicit false
set_option maxHeartbeats 100000

def parameters (code : List Function) : Bool := code.all fun f=>
  if f.name="rat" then decide (f.parameters=[("U","n"),("U","d")])
  else if f.name="divN" then decide (f.parameters=[("I","a"),("unsigned int","n")])
  else true

/-- Only installation of actual literal source bodies and checked parameter
metadata. These are source applicability conditions, never output premises. -/
structure Library (code : List Function) : Prop where
  zero : Generated.f_zero∈code
  unit : Generated.f_unit∈code
  add : Generated.f_add∈code
  mul : Generated.f_mul∈code
  divI : Generated.f_divI∈code
  divN : Generated.f_divN∈code
  positiveSub : Generated.f_positiveSub∈code
  rat : Generated.f_rat∈code
  addU : Generated.f_addU∈code
  mulU : Generated.f_mulU∈code
  ceilDiv : Generated.f_ceilDiv∈code
  arithmeticParameters : ArithmeticService.parameters code=true
  mixedParameters : parameters code=true

theorem generated_parameters : parameters Generated.functions=true := by decide +kernel

theorem rat_parameters (code : List Function) (checked : parameters code=true)
    (f : Function) (member : f∈code) (named : f.name="rat") :
    f.parameters=[("U","n"),("U","d")] := by
  have h:=(List.all_eq_true.mp checked) f member
  simpa [named] using h

theorem divN_parameters (code : List Function) (checked : parameters code=true)
    (f : Function) (member : f∈code) (named : f.name="divN") :
    f.parameters=[("I","a"),("unsigned int","n")] := by
  have h:=(List.all_eq_true.mp checked) f member
  simpa [named] using h

end SynergyC.ComputableIntervalService
