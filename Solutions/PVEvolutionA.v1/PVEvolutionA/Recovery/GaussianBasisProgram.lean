/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianQuadrature
namespace PVEvolutionA.Recovery.GaussianBasis
open LeanCert.Core LeanCert.Engine
set_option maxHeartbeats 0
structure Spec where
  n : ℕ
  k : ℕ
  start : ℚ
  step : ℚ
  cap : ℚ
  step_nonneg : 0≤step
  side : k=0 ∨ 0≤start

def cells : ℕ := 32768
def spec : Fin 18→Spec := ![
  ⟨8,0,-20,20/32768,2589157/10000000,by norm_num,by norm_num⟩,
  ⟨2,0,-20,20/32768,3776900/10000000,by norm_num,by norm_num⟩,
  ⟨7,0,-20,20/32768,2733400/10000000,by norm_num,by norm_num⟩,
  ⟨1,0,-20,20/32768,4085582/10000000,by norm_num,by norm_num⟩,
  ⟨6,0,-20,20/32768,2894260/10000000,by norm_num,by norm_num⟩,
  ⟨0,0,-20,20/32768,4447428/10000000,by norm_num,by norm_num⟩,
  ⟨8,0,0,3/32768,45991734/10000000,by norm_num,by norm_num⟩,
  ⟨2,0,0,3/32768,20700624/10000000,by norm_num,by norm_num⟩,
  ⟨7,0,0,3/32768,39880343/10000000,by norm_num,by norm_num⟩,
  ⟨1,0,0,3/32768,18366412/10000000,by norm_num,by norm_num⟩,
  ⟨6,0,0,3/32768,34712075/10000000,by norm_num,by norm_num⟩,
  ⟨0,0,0,3/32768,16357627/10000000,by norm_num,by norm_num⟩,
  ⟨8,1,0,3/32768,39863114/10000000,by norm_num,by norm_num⟩,
  ⟨2,1,0,3/32768,15097400/10000000,by norm_num,by norm_num⟩,
  ⟨8,2,0,3/32768,40752931/10000000,by norm_num,by norm_num⟩,
  ⟨2,2,0,3/32768,13866721/10000000,by norm_num,by norm_num⟩,
  ⟨7,1,0,3/32768,33665206/10000000,by norm_num,by norm_num⟩,
  ⟨1,1,0,3/32768,12973729/10000000,by norm_num,by norm_num⟩]

def row (i : Fin 18) : WinnerProgramA.Row :=
  ⟨Gaussian.cellExpr (spec i).n (spec i).k (spec i).start (spec i).step,cells⟩

def output (i : Fin 18) := WinnerProgramA.run [row i]

theorem execution (i : Fin 18) : WinnerProgramA.Exec [row i] (output i) := rfl
end PVEvolutionA.Recovery.GaussianBasis
