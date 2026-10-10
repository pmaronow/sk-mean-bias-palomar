module
public import QuantitativePaper.MovingScoreQuantileIntegral
public import FourPapersCommon.MovingCutoffChoice

@[expose] public section

/-! The paper's literal integrated spin-score variance has all three rates. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

def movingScoreQuantileConstant : ℝ := 1+16384/(1-(2 : ℝ)^(-(1/3 : ℝ)))

theorem one_le_movingScoreQuantileConstant : 1 ≤ movingScoreQuantileConstant := by
  have hρ : (2 : ℝ)^(-(1/3 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  unfold movingScoreQuantileConstant
  have hp : 0 ≤ 16384/(1-(2 : ℝ)^(-(1/3 : ℝ))) := div_nonneg (by norm_num) (sub_pos.mpr hρ).le
  linarith

theorem vectorInterpolationScoreVariance_le_one (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t ≤ 1) (hs : s ∈ Icc (0 : ℝ) 1) :
    vectorInterpolationScoreVariance (n := n) μ s β t ht ≤ 1 := by
  have h := integral_mono (integrable_vectorInterpolationScoreVariance (n := n) μ s β t ht)
    (integrable_const (1 : ℝ)) (fun q => variance_vectorMeasureOverlapScore_le_one μ β t s ht q)
  rw [integral_const] at h
  simp only [smul_eq_mul, mul_one, Measure.real, parisiFreeMeasure_univ,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2)] at h
  exact h.trans (by linarith [hs.1])

theorem vector_moving_score_quantile_rate (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) :
    vectorInterpolationScoreVariance (n := n) μ s β t ht.le ≤
      movingScoreQuantileConstant*min 1 (min (((n : ℝ)*((1-t)*β^2))^(-(1/2 : ℝ)))
        (((n : ℝ)*((1-t)*β^2))^(-(2/3 : ℝ))*s^(-(1/3 : ℝ)))) := by
  let M := (n : ℝ)*((1-t)*β^2)
  have hM : 0 < M := mul_pos (Nat.cast_pos.mpr hn) (mul_pos (sub_pos.mpr ht) (sq_pos_of_ne_zero hβ))
  by_cases hsmall : M ≤ 1
  · rw [moving_rate_subcritical M s ⟨hM, hsmall⟩ ⟨hs.1, hs.2.le⟩, mul_one]
    exact (vectorInterpolationScoreVariance_le_one μ s β t ht.le ⟨hs.1.le, hs.2.le⟩).trans
      one_le_movingScoreQuantileConstant
  have hlarge : 1 < M := lt_of_not_ge hsmall
  let u := movingQuantileCutoff M s
  have hU := movingQuantileCutoff_supercritical M s hM hs.1
  have hu : u ∈ Icc s 1 := ⟨le_max_left _ _, (movingQuantileCutoff_below_one M s hlarge hs.2).le⟩
  have hw := vector_moving_score_quantile_integral hn μ s β t hβ ht hs hμ hmin u hu hU.2
  have hinit := movingQuantileCutoff_initial_length M s hM hs.1.le
  have hrate := movingQuantileCutoff_rate_eq_min M s hM hs.1
  have hminRate : min 1 (min (M^(-(1/2 : ℝ))) (M^(-(2/3 : ℝ))*s^(-(1/3 : ℝ)))) =
      min (M^(-(1/2 : ℝ))) (M^(-(2/3 : ℝ))*s^(-(1/3 : ℝ))) :=
    min_eq_right ((min_le_left _ _).trans
      (Real.rpow_lt_one_of_one_lt_of_neg hlarge (by norm_num : -(1/2 : ℝ) < 0)).le)
  rw [hminRate, ← hrate]
  exact hw.trans (by dsimp only [movingScoreQuantileConstant]; nlinarith)

end QuantitativePaper
