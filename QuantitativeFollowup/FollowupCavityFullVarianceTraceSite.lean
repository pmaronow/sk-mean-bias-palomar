module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceEndpoint
public import QuantitativeFollowup.VectorCubicFreeMeasure
public import FourPapersCommon.ParameterVarianceMeasurability

@[expose] public section

/-! The genuine integrated one-site variance and its sharp bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem measurable_vectorMeasureSiteVariance (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (i : Fin n) :
    Measurable (fun q : Paper.Overlap => variance (vectorMeasureSiteSquare μ β t ht q i)
      (vectorMeasureDisorderTilt μ β t a)) := by
  letI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hcont : ∀sample : VectorDisorderBrownianSample n,
      Continuous (fun q : Paper.Overlap => vectorMeasureSpinMean μ β t ht q sample) :=
    continuous_vectorMeasureSpinMean_path μ β t ht
  have hmeas : ∀q : Paper.Overlap,
      Measurable (fun sample : VectorDisorderBrownianSample n =>
        vectorMeasureSpinMean μ β t ht q sample) := fun q =>
    (adapted_vectorMeasureSpinMean μ β t ht q).mono
      ((vectorBrownianFiltration n).le _) le_rfl
  have hM : Measurable (Function.uncurry (fun (q : Paper.Overlap)
      (sample : VectorDisorderBrownianSample n) => vectorMeasureSpinMean μ β t ht q sample)) :=
    measurable_uncurry_of_continuous_of_measurable hcont hmeas
  have hm : Measurable (fun p : Paper.Overlap × VectorDisorderBrownianSample n =>
      vectorMeasureSiteSquare μ β t ht p.1 i p.2) := by
    exact (((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i).measurable.comp hM).pow_const 2)
  exact measurable_parameter_variance
    (fun p : Paper.Overlap × VectorDisorderBrownianSample n => vectorMeasureSiteSquare μ β t ht p.1 i p.2)
    hm (fun q => memLp_vectorMeasureSiteSquare μ β t a ht q i)

theorem vectorMeasureSiteVariance_bounds (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) (i : Fin n) :
    variance (vectorMeasureSiteSquare μ β t ht q i) (vectorMeasureDisorderTilt μ β t a)
      ∈ Icc (0 : ℝ) (1/4) := by
  haveI := vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  refine ⟨variance_nonneg _ _, ?_⟩
  have h := variance_le_sq_of_bounded (μ:=vectorMeasureDisorderTilt (n:=n) μ β t a)
    (.of_forall (vectorMeasureSiteSquare_bounds μ β t ht q i))
    (measurable_vectorMeasureSiteSquare μ β t ht q i).aemeasurable
  norm_num at h
  exact h

theorem integrable_vectorMeasureSiteVariance (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (i : Fin n) (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] :
    Integrable (fun q : Paper.Overlap => variance (vectorMeasureSiteSquare μ β t ht q i)
      (vectorMeasureDisorderTilt μ β t a)) ν := by
  apply (integrable_const (1/4 : ℝ)).mono'
    (measurable_vectorMeasureSiteVariance μ β t a ht i).aestronglyMeasurable
  exact .of_forall fun q => by
    rw [Real.norm_of_nonneg (vectorMeasureSiteVariance_bounds μ β t a ht q i).1]
    exact (vectorMeasureSiteVariance_bounds μ β t a ht q i).2

def followupCavitySiteVariance (n : ℕ) (β ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) : ℝ :=
  ∫q : Paper.Overlap, variance (vectorMeasureSiteSquare μ β (1-ρ) (by linarith [hρ.1])
    q (Fin.last n)) (vectorMeasureDisorderTilt μ β (1-ρ) a) ∂parisiFreeMeasure μ a

theorem followupCavitySiteVariance_bounds (n : ℕ) (β ρ : ℝ) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    followupCavitySiteVariance n β ρ hρ μ a ∈ Icc (0 : ℝ) (1/4) := by
  refine ⟨integral_nonneg fun q => variance_nonneg _ _, ?_⟩
  have h := integral_mono (integrable_vectorMeasureSiteVariance μ β (1-ρ) a
    (by linarith [hρ.1]) (Fin.last n) (parisiFreeMeasure μ a)) (integrable_const (1/4 : ℝ))
    (fun q => (vectorMeasureSiteVariance_bounds μ β (1-ρ) a (by linarith [hρ.1]) q (Fin.last n)).2)
  rw [integral_const, Measure.real, parisiFreeMeasure_univ,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)] at h
  exact h.trans (by simp only [smul_eq_mul]; nlinarith [ha.1])

end QuantitativeFollowup
