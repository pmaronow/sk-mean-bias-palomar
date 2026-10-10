module
public import QuantitativePaper.VectorLocalScoreVariance
public import QuantitativePaper.VectorConditionalReplicaMoments
public import QuantitativePaper.SpinMatrixDefectAlgebra
public import QuantitativePaper.VectorSupportCovarianceSquare
public import QuantitativePaper.VectorMeanOverlapNorm

@[expose] public section

/-! The literal conditional two-replica defect decomposition, and its local
trace-plus-four-score-variance consequence on genuine minimizing free support. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set FourPapersCommon QuantitativeFollowup
open scoped NNReal BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorConditionalReplicaMatrixDefect_expansion (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) :
    vectorConditionalReplicaMatrixDefect μ β t a ht q sample=
      Matrix.trace (vectorMeasureSpinCovariance μ β t a ht q sample*
        vectorMeasureSpinCovariance μ β t a ht q sample)/(n:ℝ)^2+
      2*(vectorMeasureCovarianceQuadratic μ β t a ht q sample
        (vectorMeasureSpinMean μ β t ht q sample)/(n:ℝ)^2)+
      (‖vectorMeasureSpinMean μ β t ht q sample‖^2/(n:ℝ)-(q:ℝ))^2 := by
  unfold vectorConditionalReplicaMatrixDefect
  rw [spin_matrix_defect_expansion _ (vectorMeasureSpinCovariance_symmetric μ β t a ht q sample)]
  simp only [vectorMeasureCovarianceQuadratic,EuclideanSpace.real_norm_sq_eq,
    one_div,div_eq_mul_inv,inv_pow]
  ring

theorem vectorConditionalReplicaDefect_decomposition (hn : 0<n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) :
    vectorConditionalReplicaDefect (n:=n) μ β t a ht.le q=
      (∫sample : VectorDisorderBrownianSample n,Matrix.trace
        (vectorMeasureSpinCovariance μ β t a ht.le q sample*
          vectorMeasureSpinCovariance μ β t a ht.le q sample)∂vectorMeasureDisorderTilt μ β t a)/(n:ℝ)^2+
      2*(∫z : VectorMarkedSample n,vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
        (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2∂vectorMeasureSpinPathLaw μ β t a ht.le)+
      (∫z : VectorMarkedSample n,(vectorSelfOverlap μ β t ht.le q z-(q:ℝ))^2
        ∂vectorMeasureSpinPathLaw μ β t a ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le
  let T:=fun sample : VectorDisorderBrownianSample n=>Matrix.trace
    (vectorMeasureSpinCovariance μ β t a ht.le q sample*vectorMeasureSpinCovariance μ β t a ht.le q sample)
  have hTi:=integrable_vectorMeasureSpinCovariance_trace_square (n:=n) μ β t a ht.le q
  have hTj : Integrable (fun z : VectorMarkedSample n=>T z.1/(n:ℝ)^2) J :=
    ((measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).integrable_comp_of_integrable hTi).div_const _
  have hcond:=condVar_vectorMeasureOverlapScore (n:=n) μ β t a hβ ht q
  have hQi : Integrable (fun z : VectorMarkedSample n=>vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
      (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2) J:=integrable_condVar.congr hcond
  have hSq:=memLp_vectorCenteredSelfOverlap hn μ β t a ht.le q
  have hSi : Integrable (fun z : VectorMarkedSample n=>(vectorSelfOverlap μ β t ht.le q z-(q:ℝ))^2) J:=
    hSq.integrable_sq
  rw [vectorConditionalReplicaDefect_eq_matrix_integral hn μ β t a hβ ht q]
  simp_rw [vectorConditionalReplicaMatrixDefect_expansion]
  change (∫z : VectorMarkedSample n,T z.1/(n:ℝ)^2+
      2*(vectorMeasureCovarianceQuadratic μ β t a ht.le q z.1
        (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2)+
      (vectorSelfOverlap μ β t ht.le q z-(q:ℝ))^2∂J)=_
  have hadd:=integral_add (hTj.add (hQi.const_mul 2)) hSi
  have hfirst:=integral_add hTj (hQi.const_mul 2)
  simp only [Pi.add_apply] at hadd hfirst
  rw [hadd,hfirst,integral_const_mul,integral_div]
  have hTm : Measurable T := by
    dsimp only [T,Matrix.trace,Matrix.diag,Matrix.mul_apply]
    exact Finset.measurable_sum _ fun i _=>Finset.measurable_sum _ fun j _=>
      (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q i j).mul
        (measurable_vectorMeasureSpinCovariance_entry μ β t a ht.le q j i)
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t a ht.le T hTm]

theorem vectorSelfOverlap_mean_on_free_support (hn : 0<n) (μ : Paper.ParisiMeasure)
    (s β t : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    (∫z : VectorMarkedSample n,vectorSelfOverlap μ β t ht.le q z∂vectorMeasureSpinPathLaw μ β t s ht.le)=(q:ℝ) := by
  have hM:=integrable_vectorMeasureSpinMean_norm_sq (n:=n) μ β t s ht.le q
  have hMm : Measurable (fun sample : VectorDisorderBrownianSample n=>‖vectorMeasureSpinMean μ β t ht.le q sample‖^2):=
    ((adapted_vectorMeasureSpinMean μ β t ht.le q).mono ((vectorBrownianFiltration n).le _) le_rfl).norm.pow_const 2
  dsimp only [vectorSelfOverlap]
  rw [integral_div,integral_vectorMeasureSpinPathLaw_sample μ β t s ht.le _ hMm,
    vector_free_support_norm_contact hn μ s ⟨hs.1.le,hs.2⟩ hμ β t s hβ ht hs.1.le hmin q hq]
  have hnR : (n:ℝ)≠0:=by positivity
  field_simp

theorem vectorConditionalReplicaDefect_le_trace_add_score_variance (hn : 0<n)
    (μ : Paper.ParisiMeasure) (s β t : ℝ) (hs : s∈Ioo (0:ℝ) 1) (hμ : μ∈scalarFloor s)
    (hβ : β≠0) (ht : t<1)
    (hmin : ∀ν∈scalarFloor s,vectorMeasureFunctional n μ β t s≤vectorMeasureFunctional n ν β t s)
    (q : Paper.Overlap) (hq : q∈(parisiFreeMeasure μ s).support) :
    vectorConditionalReplicaDefect (n:=n) μ β t s ht.le q≤
      (∫sample : VectorDisorderBrownianSample n,Matrix.trace
        (vectorMeasureSpinCovariance μ β t s ht.le q sample*
          vectorMeasureSpinCovariance μ β t s ht.le q sample)∂vectorMeasureDisorderTilt μ β t s)/(n:ℝ)^2+
      4*variance (vectorMeasureOverlapScore (n:=n) μ β t ht.le q)
        (vectorMeasureSpinPathLaw μ β t s ht.le) := by
  let J:=vectorMeasureSpinPathLaw (n:=n) μ β t s ht.le
  have hmean:=vectorSelfOverlap_mean_on_free_support hn μ s β t hs hμ hβ ht hmin q hq
  have hv:=variance_eq_integral (μ:=J) (measurable_vectorSelfOverlap (n:=n) μ β t ht.le q).aemeasurable
  rw [hmean] at hv
  have htot:=variance_vectorMeasureOverlapScore_total (n:=n) μ β t s hβ ht q
  have hdec:=vectorConditionalReplicaDefect_decomposition hn μ β t s hβ ht q
  rw [←hv] at hdec
  have hj : 0≤∫z : VectorMarkedSample n,vectorMeasureCovarianceQuadratic μ β t s ht.le q z.1
      (vectorMeasureSpinMean μ β t ht.le q z.1)/(n:ℝ)^2∂J := by
    rw [←integral_congr_ae (condVar_vectorMeasureOverlapScore (n:=n) μ β t s hβ ht q)]
    exact integral_nonneg_of_ae (condExp_nonneg (.of_forall fun z=>sq_nonneg _))
  linarith

end QuantitativePaper
