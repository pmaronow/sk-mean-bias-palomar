module
public import QuantitativePaper.VectorReplicaDefectDecomposition
public import QuantitativePaper.VectorCovarianceTraceMeasurability
public import QuantitativeFollowup.VectorSelfOverlapMoments
public import FourPapersCommon.ParameterVarianceMeasurability

@[expose] public section

/-! Measurable actual score variance and conditional-replica defect curves. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

theorem measurable_vectorMeasureOverlapScore_joint (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) :
    Measurable (fun p : Paper.Overlap×VectorMarkedSample n=>vectorMeasureOverlapScore μ β t ht p.1 p.2) := by
  have hM:=measurable_vectorMeasureSpinMean_joint (n:=n) μ β t ht
  have hdot : Measurable (fun p : Paper.Overlap×VectorMarkedSample n=>
      fieldDot (vectorMeasureSpinMean μ β t ht p.1 p.2.1) p.2.2) := by
    unfold fieldDot
    exact Finset.measurable_sum _ fun i _=>
      (((PiLp.continuous_apply 2 (fun _ : Fin n=>ℝ) i).measurable.comp hM).mul
        ((measurable_of_finite (fun σ : Configuration n=>Paper.spinSign (σ i))).comp
          (measurable_snd.comp measurable_snd)))
  exact (hdot.sub ((hM.norm.pow_const 2).div_const 2)).div_const _

theorem measurable_variance_vectorMeasureOverlapScore (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    Measurable (fun q : Paper.Overlap=>variance (vectorMeasureOverlapScore (n:=n) μ β t ht q)
      (vectorMeasureSpinPathLaw μ β t a ht)) := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  exact measurable_parameter_variance
    (fun p : Paper.Overlap×VectorMarkedSample n=>vectorMeasureOverlapScore μ β t ht p.1 p.2)
    (measurable_vectorMeasureOverlapScore_joint μ β t ht)
    (fun q=>memLp_vectorMeasureOverlapScore μ β t a ht q)

theorem measurable_variance_vectorSelfOverlap (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) :
    Measurable (fun q : Paper.Overlap=>variance (vectorSelfOverlap (n:=n) μ β t ht q)
      (vectorMeasureSpinPathLaw μ β t a ht)) := by
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hM:=measurable_vectorMeasureSpinMean_joint (n:=n) μ β t ht
  apply measurable_parameter_variance
    (fun p : Paper.Overlap×VectorMarkedSample n=>vectorSelfOverlap μ β t ht p.1 p.2)
    ((hM.norm.pow_const 2).div_const (n:ℝ))
  intro q
  change MemLp (vectorSelfOverlap (n:=n) μ β t ht q) 2 (vectorMeasureSpinPathLaw μ β t a ht)
  exact MemLp.of_bound (measurable_vectorSelfOverlap μ β t ht q).aestronglyMeasurable 1
    (.of_forall fun z=>by
      rw [Real.norm_of_nonneg (vectorSelfOverlap_bounds hn μ β t ht q z).1]
      exact (vectorSelfOverlap_bounds hn μ β t ht q z).2)

theorem measurable_vectorConditionalReplicaDefect (hn : 0<n) (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) :
    Measurable (vectorConditionalReplicaDefect (n:=n) μ β t a ht.le) := by
  have hT:=(measurable_integral_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t a ht.le).div_const
    ((n:ℝ)^2)
  have hL:=measurable_variance_vectorMeasureOverlapScore (n:=n) μ β t a ht.le
  have hS:=measurable_variance_vectorSelfOverlap hn μ β t a ht.le
  have hC:=measurable_vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht.le
  have he : vectorConditionalReplicaDefect (n:=n) μ β t a ht.le=
    fun q : Paper.Overlap=>(∫sample : VectorDisorderBrownianSample n,Matrix.trace
      (vectorMeasureSpinCovariance μ β t a ht.le q sample*vectorMeasureSpinCovariance μ β t a ht.le q sample)
        ∂vectorMeasureDisorderTilt μ β t a)/(n:ℝ)^2+
      2*variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le)-
      (1/2)*variance (vectorSelfOverlap (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t a ht.le)+
      vectorCenteredSelfOverlapSecond (n:=n) μ β t a ht.le q := by
    funext q
    have hd:=vectorConditionalReplicaDefect_decomposition hn μ β t a hβ ht q
    have hv:=variance_vectorMeasureOverlapScore_total (n:=n) μ β t a hβ ht q
    change _=_+2*(_)-(1/2)*(_)+
      (∫z : VectorMarkedSample n,(vectorSelfOverlap μ β t ht.le q z-(q:ℝ))^2
        ∂vectorMeasureSpinPathLaw μ β t a ht.le)
    linarith
  rw [he]
  exact ((hT.add (measurable_const.mul hL)).sub (measurable_const.mul hS)).add hC

end QuantitativePaper
