module
public import QuantitativePaper.MovingTraceRate
public import QuantitativePaper.MovingScoreQuantileRate

@[expose] public section

/-! Lemma 4.1 for the literal actual conditional-replica defect. The score
term uses Var(L), and every covariance, contact and shell input is proved. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativeFollowup
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

def movingCutoffDefectConstant : ℝ := 2+4*movingScoreQuantileConstant

theorem movingCutoffDefectConstant_pos : 0 < movingCutoffDefectConstant := by
  unfold movingCutoffDefectConstant
  linarith [one_le_movingScoreQuantileConstant]

theorem vector_moving_cutoff (hn : 0 < n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) (hs : s ∈ Ioo (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hmin : ∀ ν ∈ scalarFloor s, vectorMeasureFunctional n μ β t s ≤ vectorMeasureFunctional n ν β t s) :
    vectorInterpolationDefect (n := n) μ s β t ht.le ≤
      movingCutoffDefectConstant*min 1 (min (((n : ℝ)*((1-t)*β^2))^(-(1/2 : ℝ)))
        (((n : ℝ)*((1-t)*β^2))^(-(2/3 : ℝ))*s^(-(1/3 : ℝ)))) := by
  have hD := vectorInterpolationDefect_le_trace_add_score_variance hn μ s β t hs hμ hβ ht hmin
  have hA := vectorInterpolationTraceError_moving_rate hn μ s β t hs hμ hβ ht hmin
  have hW := vector_moving_score_quantile_rate hn μ s β t hβ ht hs hμ hmin
  unfold movingCutoffDefectConstant
  linarith

end QuantitativePaper
