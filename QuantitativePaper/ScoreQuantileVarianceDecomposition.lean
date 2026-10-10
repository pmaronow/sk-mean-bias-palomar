module
public import QuantitativePaper.ScoreQuantileRefinementResidual
public import QuantitativePaper.RefinedQuantileShell
public import QuantitativeFollowup.VectorCubicFreeMeasure

@[expose] public section

/-! The literal terminal score variance splits into its actual conditional
covariance and one quarter of the variance of its conditional mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativeFollowup
open scoped NNReal ENNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem variance_vectorMeasureOverlapScore_eq_mean_covariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le)=
      vectorMeanDirectionCovariance (n:=n) μ β t a ht.le q+
        (1/4)*variance (vectorSelfOverlap (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le) := by
  have hc:=measurable_vectorMeasureCovarianceQuadratic_random (n:=n) μ β t a ht.le q
    (vectorMeasureSpinMean μ β t ht.le q)
    (fun i=>(adapted_vectorMeasureSpinMean_component μ β t ht.le q i).mono
      ((vectorBrownianFiltration n).le _) le_rfl)
  rw [variance_vectorMeasureOverlapScore_total μ β t a hβ ht q,integral_div,
    integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le _ hc]
  rfl

theorem measurable_scoreVariance_via_total (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    Measurable (fun q=>variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q)
      (vectorMeasureSpinPathLaw μ β t a ht.le)) := by
  have h:=(measurable_vectorMeanDirectionCovariance (n:=n) μ β t a hβ ht).add
    ((QuantitativeFollowup.measurable_variance_vectorSelfOverlap hn μ β t a ht.le).const_mul (1/4))
  convert h using 1
  funext q
  exact variance_vectorMeasureOverlapScore_eq_mean_covariance μ β t a hβ ht q

theorem integrableOn_variance_vectorSelfOverlap (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (I : Set ℝ) [IsFiniteMeasure (volume.restrict I)] (s : ℝ) :
    IntegrableOn (fun v=>variance (vectorSelfOverlap (n:=n) μ β t ht (parisiFreeQuantile μ s v))
      (vectorMeasureSpinPathLaw μ β t a ht)) I := by
  let :=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  apply Integrable.of_bound
    ((QuantitativeFollowup.measurable_variance_vectorSelfOverlap hn μ β t a ht).comp
      (parisiFreeQuantile_measurable μ s)).aestronglyMeasurable 1
  refine .of_forall fun v=>?_ 
  simp only [Function.comp_def]
  rw [Real.norm_of_nonneg (variance_nonneg _ _)]
  have hS : MemLp (vectorSelfOverlap (n:=n) μ β t ht (parisiFreeQuantile μ s v)) 2
      (vectorMeasureSpinPathLaw μ β t a ht) :=
    MemLp.of_bound (measurable_vectorSelfOverlap μ β t ht _).aestronglyMeasurable 1
      (.of_forall fun z=>by
        rw [Real.norm_of_nonneg (vectorSelfOverlap_bounds hn μ β t ht _ z).1]
        exact (vectorSelfOverlap_bounds hn μ β t ht _ z).2)
  have hb:=variance_le_expectation_sq hS.aestronglyMeasurable
  have hi:=hS.integrable_sq
  have hc:=integral_mono hi (integrable_const (1:ℝ)) (fun z=>by
    have he:=vectorSelfOverlap_bounds hn μ β t ht (parisiFreeQuantile μ s v) z
    nlinarith)
  simp only [integral_const,probReal_univ,one_smul] at hc
  exact hb.trans hc

end QuantitativePaper
