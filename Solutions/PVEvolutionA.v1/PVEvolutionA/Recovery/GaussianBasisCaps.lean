/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import PVEvolutionA.Recovery.GaussianBasisSound
import PVEvolutionA.Recovery.GaussianCombination
namespace PVEvolutionA.Recovery.GaussianBasis
open Real Set MeasureTheory
set_option maxHeartbeats 0
def caps : Fin 12→ℚ := ![48580891/10000000,24477524/10000000,42613743/10000000,22451994/10000000,37606335/10000000,20805055/10000000,39863114/10000000,15097400/10000000,40752931/10000000,13866721/10000000,33665206/10000000,12973729/10000000]

theorem integral_caps
    (accepted : ∀j:Fin 18,WinnerProgramA.acceptUpper (output j) [(spec j).cap]=true)
    (i : Fin 12) : Gaussian.basisIntegral i≤(caps i:ℝ) := by
  fin_cases i
  · have hp := integral_upper (6:Fin 18) (accepted 6)
    have hn := integral_upper (0:Fin 18) (accepted 0)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (7:Fin 18) (accepted 7)
    have hn := integral_upper (1:Fin 18) (accepted 1)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (8:Fin 18) (accepted 8)
    have hn := integral_upper (2:Fin 18) (accepted 2)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (9:Fin 18) (accepted 9)
    have hn := integral_upper (3:Fin 18) (accepted 3)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (10:Fin 18) (accepted 10)
    have hn := integral_upper (4:Fin 18) (accepted 4)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (11:Fin 18) (accepted 11)
    have hn := integral_upper (5:Fin 18) (accepted 5)
    dsimp [spec,cells] at hp hn
    norm_num at hp hn
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (12:Fin 18) (accepted 12)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (13:Fin 18) (accepted 13)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (14:Fin 18) (accepted 14)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (15:Fin 18) (accepted 15)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (16:Fin 18) (accepted 16)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith
  · have hp := integral_upper (17:Fin 18) (accepted 17)
    dsimp [spec,cells] at hp
    norm_num at hp
    norm_num [Gaussian.basisIntegral,Gaussian.basisN,Gaussian.basisK,caps]
    linarith

#print axioms integral_caps
end PVEvolutionA.Recovery.GaussianBasis
