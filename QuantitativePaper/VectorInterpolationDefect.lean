module
public import QuantitativePaper.VectorReplicaDefectMeasurability
public import QuantitativePaper.VectorCovarianceTraceTrivialBound

@[expose] public section

/-! Actual free-measure replica defect and its trace/score-variance
decomposition. All observables are those of the genuine marked diffusion law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128

def vectorInterpolationDefect (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) : ℝ:=
  ∫q,vectorConditionalReplicaDefect (n:=n) μ β t s ht q∂parisiFreeMeasure μ s

def vectorInterpolationTraceError (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) : ℝ:=
  ∫q,(∫sample : VectorDisorderBrownianSample n,Matrix.trace
    (vectorMeasureSpinCovariance μ β t s ht q sample*vectorMeasureSpinCovariance μ β t s ht q sample)
      ∂vectorMeasureDisorderTilt μ β t s)/(n:ℝ)^2∂parisiFreeMeasure μ s

def vectorInterpolationScoreVariance (μ : Paper.ParisiMeasure) (s β t : ℝ) (ht : t≤1) : ℝ:=
  ∫q,variance (vectorMeasureOverlapScore (n:=n) μ β t ht q)
    (vectorMeasureSpinPathLaw μ β t s ht)∂parisiFreeMeasure μ s

theorem variance_vectorMeasureOverlapScore_bound (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) :
    0≤variance (vectorMeasureOverlapScore (n:=n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht) ∧
    variance (vectorMeasureOverlapScore (n:=n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht)≤9/4 := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht
  letI:=vectorMeasureSpinPathLaw_probability (n:=n) μ β t a ht
  have hL:=memLp_vectorMeasureOverlapScore (n:=n) μ β t a ht q
  refine ⟨variance_nonneg _ _,?_⟩
  have hb:=integral_mono hL.integrable_sq (integrable_const (9/4:ℝ)) (fun z=>by
    have h:=abs_le.mp (vectorMeasureOverlapScore_bound μ β t ht q z)
    nlinarith)
  simp only [integral_const,probReal_univ,one_smul] at hb
  rw [variance_eq_sub hL]
  simp only [Pi.pow_apply]
  exact (sub_le_self _ (sq_nonneg _)).trans hb

theorem integrable_vectorInterpolationDefect (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) :
    Integrable (vectorConditionalReplicaDefect (n:=n) μ β t s ht.le) (parisiFreeMeasure μ s) := by
  apply (integrable_const (4:ℝ)).mono'
    (measurable_vectorConditionalReplicaDefect hn μ β t s hβ ht).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [Real.norm_of_nonneg (vectorConditionalReplicaDefect_bounds hn μ β t s ht.le q).1]
    exact (vectorConditionalReplicaDefect_bounds hn μ β t s ht.le q).2

theorem integrable_vectorInterpolationTraceError (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hβ : β≠0) (ht : t<1) :
    Integrable (fun q : Paper.Overlap=>(∫sample : VectorDisorderBrownianSample n,Matrix.trace
      (vectorMeasureSpinCovariance μ β t s ht.le q sample*vectorMeasureSpinCovariance μ β t s ht.le q sample)
        ∂vectorMeasureDisorderTilt μ β t s)/(n:ℝ)^2) (parisiFreeMeasure μ s) := by
  apply (integrable_const (1:ℝ)).mono'
    ((measurable_integral_vectorMeasureSpinCovariance_trace_square μ β t s ht.le).div_const _).aestronglyMeasurable
  exact .of_forall fun q=>by
    have hpos : 0≤∫sample : VectorDisorderBrownianSample n,Matrix.trace
        (vectorMeasureSpinCovariance μ β t s ht.le q sample*vectorMeasureSpinCovariance μ β t s ht.le q sample)
          ∂vectorMeasureDisorderTilt μ β t s := by
      apply integral_nonneg
      intro sample
      change 0≤Matrix.trace (vectorMeasureSpinCovariance μ β t s ht.le q sample*
        vectorMeasureSpinCovariance μ β t s ht.le q sample)
      rw [symmetric_matrix_square_trace _ (vectorMeasureSpinCovariance_symmetric μ β t s ht.le q sample)]
      positivity
    rw [Real.norm_of_nonneg (div_nonneg hpos (sq_nonneg _))]
    exact (div_le_one (by positivity : (0:ℝ)<(n:ℝ)^2)).mpr
      (integral_vectorMeasureSpinCovariance_trace_square_le_dimension μ β t s hβ ht q)

theorem integrable_vectorInterpolationScoreVariance (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) :
    Integrable (fun q : Paper.Overlap=>variance (vectorMeasureOverlapScore (n:=n) μ β t ht q)
      (vectorMeasureSpinPathLaw μ β t s ht)) (parisiFreeMeasure μ s) := by
  apply (integrable_const (9/4:ℝ)).mono'
    (measurable_variance_vectorMeasureOverlapScore μ β t s ht).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [Real.norm_of_nonneg (variance_vectorMeasureOverlapScore_bound μ β t s ht q).1]
    exact (variance_vectorMeasureOverlapScore_bound μ β t s ht q).2

theorem vectorInterpolationDefect_nonneg (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (ht : t≤1) : 0≤vectorInterpolationDefect (n:=n) μ s β t ht :=
  integral_nonneg fun q=>(vectorConditionalReplicaDefect_bounds hn μ β t s ht q).1

theorem vectorInterpolationDefect_le_trace_add_score_variance (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s) :
    vectorInterpolationDefect (n:=n) μ s β t ht.le≤
      vectorInterpolationTraceError (n:=n) μ s β t ht.le+4*vectorInterpolationScoreVariance (n:=n) μ s β t ht.le := by
  have hD:=integrable_vectorInterpolationDefect hn μ s β t hβ ht
  have hA:=integrable_vectorInterpolationTraceError hn μ s β t hβ ht
  have hW:=integrable_vectorInterpolationScoreVariance (n:=n) μ s β t ht.le
  have hpoint : ∀ᵐq ∂parisiFreeMeasure μ s,vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q≤
    (∫sample : VectorDisorderBrownianSample n,Matrix.trace
      (vectorMeasureSpinCovariance μ β t s ht.le q sample*vectorMeasureSpinCovariance μ β t s ht.le q sample)
        ∂vectorMeasureDisorderTilt μ β t s)/(n:ℝ)^2+
    4*variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q) (vectorMeasureSpinPathLaw μ β t s ht.le) := by
    filter_upwards [(parisiFreeMeasure μ s).support_mem_ae] with q hq
    exact vectorConditionalReplicaDefect_le_trace_add_score_variance hn μ s β t hs hμ hβ ht hmin q hq
  have h:=integral_mono_ae hD (hA.add (hW.const_mul 4)) hpoint
  have hadd:=integral_add hA (hW.const_mul 4)
  simp only [Pi.add_apply] at h
  rw [hadd,integral_const_mul] at h
  exact h

end QuantitativePaper
