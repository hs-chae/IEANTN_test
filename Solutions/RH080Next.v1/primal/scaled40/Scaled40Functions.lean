import Scaled40Sources
noncomputable section
namespace RH080Next.Scaled40
open RH080.Gaussian40
def baseF (x : ℝ) : ℝ := coeffEval normSource (Real.sqrt Real.pi*x)*Real.exp (-((Real.sqrt Real.pi*x)^2))
def baseG (x : ℝ) : ℝ := coeffEval wingSource (Real.sqrt Real.pi*x)*Real.exp (-((Real.sqrt Real.pi*x)^2))
def physicalF (x : ℝ) : ℝ := baseF ((5/4)*x)
def physicalG (x : ℝ) : ℝ := (4/5)*baseG ((4/5)*x)
end RH080Next.Scaled40
