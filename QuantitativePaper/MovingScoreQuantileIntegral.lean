module
public import QuantitativePaper.MovingScoreQuantileShell
public import QuantitativePaper.VectorInterpolationDefect
public import QuantitativePaper.VectorScoreRange
public import FourPapersCommon.DyadicQuantileIntegral

@[expose] public section

/-! Actual integrated terminal-spin score variance under the moving quantile cutoff. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
open scoped NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vector_moving_score_quantile_integral (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s)
    (u : ℝ) (hu : u ∈ Icc s 1) (hMu : 1 ≤ ((n : ℝ)*((1-t)*β^2))*u^2) :
    vectorInterpolationScoreVariance (n := n) μ s β t ht.le ≤
      (u-s)+16384/(1-(2 : ℝ)^(-(1/3 : ℝ)))*
        (((n : ℝ)*((1-t)*β^2))^(-(2/3 : ℝ))*u^(-(1/3 : ℝ))) := by
  let ψ : ℝ → ℝ := fun v => variance
    (vectorMeasureOverlapScore (n := n) μ β t ht.le (parisiFreeQuantile μ s v))
    (vectorMeasureSpinPathLaw μ β t s ht.le)
  have hψ : Measurable ψ := (measurable_variance_vectorMeasureOverlapScore μ β t s ht.le).comp
    (parisiFreeQuantile_measurable μ s)
  have hb : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1 := fun v =>
    ⟨variance_nonneg _ _, variance_vectorMeasureOverlapScore_le_one μ β t s ht.le _⟩
  have hρ : (2 : ℝ)^(-(1/3 : ℝ)) ∈ Ico (0 : ℝ) 1 :=
    ⟨(Real.rpow_pos_of_pos (by norm_num) _).le,
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)⟩
  have hsum := bounded_dyadic_quantile_integral ψ hψ hb s u hs hu
    (16384*(((n : ℝ)*((1-t)*β^2))^(-(2/3 : ℝ))*u^(-(1/3 : ℝ))))
    ((2 : ℝ)^(-(1/3 : ℝ))) hρ (fun j =>
      vector_moving_score_quantile_shell hn μ s β t hβ ht hs hμ hmin u
        (hs.1.trans_le hu.1) hMu j)
  unfold vectorInterpolationScoreVariance
  rw [integral_parisiFreeMeasure μ s _ (measurable_variance_vectorMeasureOverlapScore μ β t s ht.le),
    integral_Ioc_eq_integral_Ioo]
  convert hsum using 1 <;> ring

end QuantitativePaper
