import SourceDeficits
namespace Ramanujan640
open Real IEANTN
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem lower_component_0 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (640000000000:ℝ) ≤ t) (hu : t ≤ (1280000000000:ℝ)) :
    (-37/50:ℝ) ≤ (li t-riemannPrimeCounting t)*log t/sqrt t := by
  have h := hT (640000000000, (-37/50:ℝ), (41/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms lower_component_0

theorem upper_component_1 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (160000000000:ℝ) ≤ t) (hu : t ≤ (320000000000:ℝ)) :
    (li t-riemannPrimeCounting t)*log t/sqrt t ≤ (19/25:ℝ) := by
  have h := hT (160000000000, (-97/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms upper_component_1

theorem upper_component_2 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (160000000000:ℝ) ≤ t) (hu : t ≤ (1280000000000:ℝ)) :
    (li t-riemannPrimeCounting t)*log t/sqrt t ≤ (43/50:ℝ) := by
  by_cases h0 : t ≤ (320000000000:ℝ)
  · have h := hT (160000000000, (-97/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h1 : t ≤ (640000000000:ℝ)
  · have h := hT (320000000000, (-24/25:ℝ), (43/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  have h := hT (640000000000, (-37/50:ℝ), (41/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms upper_component_2

theorem lower_component_3 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (640000000000:ℝ) ≤ t) (hu : t ≤ (12800000000000000:ℝ)) :
    (-22/25:ℝ) ≤ (li t-riemannPrimeCounting t)*log t/sqrt t := by
  by_cases h0 : t ≤ (1280000000000:ℝ)
  · have h := hT (640000000000, (-37/50:ℝ), (41/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h1 : t ≤ (2000000000000:ℝ)
  · have h := hT (1000000000000, (-22/25:ℝ), (89/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h2 : t ≤ (4000000000000:ℝ)
  · have h := hT (2000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h3 : t ≤ (8000000000000:ℝ)
  · have h := hT (4000000000000, (-81/100:ℝ), (81/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h4 : t ≤ (16000000000000:ℝ)
  · have h := hT (8000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h5 : t ≤ (32000000000000:ℝ)
  · have h := hT (16000000000000, (-87/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h6 : t ≤ (64000000000000:ℝ)
  · have h := hT (32000000000000, (-37/50:ℝ), (1:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h7 : t ≤ (128000000000000:ℝ)
  · have h := hT (64000000000000, (-17/20:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h8 : t ≤ (200000000000000:ℝ)
  · have h := hT (100000000000000, (-43/50:ℝ), (79/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h9 : t ≤ (400000000000000:ℝ)
  · have h := hT (200000000000000, (-67/100:ℝ), (83/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h10 : t ≤ (800000000000000:ℝ)
  · have h := hT (400000000000000, (-18/25:ℝ), (4/5:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h11 : t ≤ (1600000000000000:ℝ)
  · have h := hT (800000000000000, (-87/100:ℝ), (19/20:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h12 : t ≤ (3200000000000000:ℝ)
  · have h := hT (1600000000000000, (-18/25:ℝ), (93/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h13 : t ≤ (6400000000000000:ℝ)
  · have h := hT (3200000000000000, (-4/5:ℝ), (23/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  have h := hT (6400000000000000, (-79/100:ℝ), (18/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms lower_component_3

theorem lower_component_4 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (2000000000000:ℝ) ≤ t) (hu : t ≤ (12800000000000000:ℝ)) :
    (-87/100:ℝ) ≤ (li t-riemannPrimeCounting t)*log t/sqrt t := by
  by_cases h0 : t ≤ (4000000000000:ℝ)
  · have h := hT (2000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h1 : t ≤ (8000000000000:ℝ)
  · have h := hT (4000000000000, (-81/100:ℝ), (81/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h2 : t ≤ (16000000000000:ℝ)
  · have h := hT (8000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h3 : t ≤ (32000000000000:ℝ)
  · have h := hT (16000000000000, (-87/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h4 : t ≤ (64000000000000:ℝ)
  · have h := hT (32000000000000, (-37/50:ℝ), (1:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h5 : t ≤ (128000000000000:ℝ)
  · have h := hT (64000000000000, (-17/20:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h6 : t ≤ (200000000000000:ℝ)
  · have h := hT (100000000000000, (-43/50:ℝ), (79/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h7 : t ≤ (400000000000000:ℝ)
  · have h := hT (200000000000000, (-67/100:ℝ), (83/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h8 : t ≤ (800000000000000:ℝ)
  · have h := hT (400000000000000, (-18/25:ℝ), (4/5:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h9 : t ≤ (1600000000000000:ℝ)
  · have h := hT (800000000000000, (-87/100:ℝ), (19/20:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h10 : t ≤ (3200000000000000:ℝ)
  · have h := hT (1600000000000000, (-18/25:ℝ), (93/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h11 : t ≤ (6400000000000000:ℝ)
  · have h := hT (3200000000000000, (-4/5:ℝ), (23/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  have h := hT (6400000000000000, (-79/100:ℝ), (18/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms lower_component_4

theorem upper_component_5 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (160000000000:ℝ) ≤ t) (hu : t ≤ (32000000000000:ℝ)) :
    (li t-riemannPrimeCounting t)*log t/sqrt t ≤ (89/100:ℝ) := by
  by_cases h0 : t ≤ (320000000000:ℝ)
  · have h := hT (160000000000, (-97/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h1 : t ≤ (640000000000:ℝ)
  · have h := hT (320000000000, (-24/25:ℝ), (43/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h2 : t ≤ (1280000000000:ℝ)
  · have h := hT (640000000000, (-37/50:ℝ), (41/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h3 : t ≤ (2000000000000:ℝ)
  · have h := hT (1000000000000, (-22/25:ℝ), (89/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h4 : t ≤ (4000000000000:ℝ)
  · have h := hT (2000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h5 : t ≤ (8000000000000:ℝ)
  · have h := hT (4000000000000, (-81/100:ℝ), (81/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h6 : t ≤ (16000000000000:ℝ)
  · have h := hT (8000000000000, (-87/100:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  have h := hT (16000000000000, (-87/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms upper_component_5

theorem upper_component_6 (hT : Buthe.v1.table_2_interval_bounds) {t : ℝ}
    (hl : (64000000000000:ℝ) ≤ t) (hu : t ≤ (5120000000000000000:ℝ)) :
    (li t-riemannPrimeCounting t)*log t/sqrt t ≤ (49/50:ℝ) := by
  by_cases h0 : t ≤ (128000000000000:ℝ)
  · have h := hT (64000000000000, (-17/20:ℝ), (21/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h1 : t ≤ (200000000000000:ℝ)
  · have h := hT (100000000000000, (-43/50:ℝ), (79/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h2 : t ≤ (400000000000000:ℝ)
  · have h := hT (200000000000000, (-67/100:ℝ), (83/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h3 : t ≤ (800000000000000:ℝ)
  · have h := hT (400000000000000, (-18/25:ℝ), (4/5:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h4 : t ≤ (1600000000000000:ℝ)
  · have h := hT (800000000000000, (-87/100:ℝ), (19/20:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h5 : t ≤ (3200000000000000:ℝ)
  · have h := hT (1600000000000000, (-18/25:ℝ), (93/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h6 : t ≤ (6400000000000000:ℝ)
  · have h := hT (3200000000000000, (-4/5:ℝ), (23/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h7 : t ≤ (12800000000000000:ℝ)
  · have h := hT (6400000000000000, (-79/100:ℝ), (18/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h8 : t ≤ (20000000000000000:ℝ)
  · have h := hT (10000000000000000, (-47/50:ℝ), (4/5:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h9 : t ≤ (40000000000000000:ℝ)
  · have h := hT (20000000000000000, (-93/100:ℝ), (19/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h10 : t ≤ (80000000000000000:ℝ)
  · have h := hT (40000000000000000, (-71/100:ℝ), (79/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h11 : t ≤ (160000000000000000:ℝ)
  · have h := hT (80000000000000000, (-22/25:ℝ), (83/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h12 : t ≤ (320000000000000000:ℝ)
  · have h := hT (160000000000000000, (-77/100:ℝ), (49/50:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h13 : t ≤ (640000000000000000:ℝ)
  · have h := hT (320000000000000000, (-21/25:ℝ), (77/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h14 : t ≤ (1280000000000000000:ℝ)
  · have h := hT (640000000000000000, (-1:ℝ), (22/25:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  by_cases h15 : t ≤ (2560000000000000000:ℝ)
  · have h := hT (1280000000000000000, (-1:ℝ), (4/5:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
    linarith [h.1, h.2]
  have h := hT (2560000000000000000, (-87/100:ℝ), (91/100:ℝ)) (by norm_num [Buthe.v1.table_2]) t (by linarith) (by linarith)
  linarith [h.1, h.2]
#print axioms upper_component_6
end Ramanujan640
