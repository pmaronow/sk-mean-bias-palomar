module
public import QuantitativeFollowup.StandardSKAnisotropicHessian
public import QuantitativePaper.VectorMeasureRandomReaction
public import QuantitativePaper.VectorMeasureAffineScoreVarianceBound
public import QuantitativePaper.VectorMeasureKernelMean

@[expose] public section

/-! Literal selected-coordinate observables for the printed SK law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def standardSKWeightedSelfOverlap (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (κ : Paper.Overlap→ℝ) (J : Finset (Fin n)) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∫q,κ q*anisotropicSelectedMeanSquare J (vectorMeasureSpinMean μ β t ht q sample)
    ∂parisiFreeMeasure μ a

def standardSKSelectedMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : Field n :=
  anisotropicSelectedFieldMap J (vectorMeasureSpinMean μ β t ht q sample)

def standardSKSelectedHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  inner ℝ (vectorMeasureHessianProcess μ β t ht q sample
    (standardSKSelectedMean μ β t ht J q sample)) (standardSKSelectedMean μ β t ht J q sample)

def standardSKSelectedCovarianceEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (J : Finset (Fin n)) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorMeasureCovarianceQuadratic μ β t a ht q sample (standardSKSelectedMean μ β t ht J q sample)

theorem standardSKAnisotropicWeightedSelfOverlap (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (κ : Paper.Overlap→ℝ) (J : Finset (Fin n))
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicWeightedSelfOverlap (standardSKAnisotropicModel n β t hβ ht) μ a κ J sample=
      standardSKWeightedSelfOverlap μ β t a ht.le κ J (standardSKSampleCompression sample) := by
  unfold anisotropicWeightedSelfOverlap standardSKWeightedSelfOverlap
  congr 1;funext q
  rw [standardSKAnisotropicProcessMagnetization]
  rfl

theorem standardSKAnisotropicHessianEnergy (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (J : Finset (Fin n)) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    anisotropicProcessHessianEnergy (standardSKAnisotropicModel n β t hβ ht) μ J q sample=
      standardSKSelectedHessianEnergy μ β t ht.le J q (standardSKSampleCompression sample) := by
  unfold anisotropicProcessHessianEnergy anisotropicSelectedParameterDirection
  simp only [ContinuousLinearMap.comp_apply]
  change fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential _ μ q))
    (anisotropicProcessParameter _ μ q sample)
    (anisotropicFieldInjection n (anisotropicSelectedFieldMap J (anisotropicProcessMagnetization _ μ q sample)))
    (anisotropicFieldInjection n (anisotropicSelectedFieldMap J (anisotropicProcessMagnetization _ μ q sample)))=_
  unfold anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    standardSKAnisotropicFieldHessian,standardSKAnisotropicProcessMagnetization,
    standardSKAnisotropicMeasureState μ β t hβ ht q q.property]
  rfl

theorem measurable_standardSKSpinMean_joint (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1) :
    Measurable (fun z : Paper.Overlap×VectorDisorderBrownianSample n=>vectorMeasureSpinMean μ β t ht z.1 z.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (continuous_vectorMeasureSpinMean_path μ β t ht)
    (fun q=>(adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl)

theorem measurable_standardSKWeightedSelfOverlap (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hκ : Measurable κ) (J : Finset (Fin n)) :
    Measurable (standardSKWeightedSelfOverlap (n:=n) μ β t a ht κ J) := by
  have hm := (hκ.comp measurable_fst).mul
    ((continuous_anisotropicSelectedMeanSquare J).measurable.comp (measurable_standardSKSpinMean_joint μ β t ht))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

theorem measurable_standardSKWeightedSelfOverlap_L2 (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (κ : Paper.Overlap→ℝ) (hL : MemLp κ 2 (parisiFreeMeasure μ a))
    (J : Finset (Fin n)) : Measurable (standardSKWeightedSelfOverlap (n:=n) μ β t a ht κ J) := by
  let η:=hL.aestronglyMeasurable.mk κ
  have he : κ=ᵐ[parisiFreeMeasure μ a]η:=hL.aestronglyMeasurable.ae_eq_mk
  have hfun : standardSKWeightedSelfOverlap (n:=n) μ β t a ht κ J=
      standardSKWeightedSelfOverlap μ β t a ht η J := by
    funext sample;apply integral_congr_ae
    exact he.mono fun q hq=>by dsimp only;rw [hq]
  rw [hfun]
  exact measurable_standardSKWeightedSelfOverlap μ β t a ht η
    hL.aestronglyMeasurable.stronglyMeasurable_mk.measurable J

theorem measurable_standardSKSelectedMean (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (J : Finset (Fin n)) (q : Paper.Overlap) :
    Measurable (standardSKSelectedMean (n:=n) μ β t ht J q) :=
  (anisotropicSelectedFieldMap J).continuous.measurable.comp
    ((adapted_vectorMeasureSpinMean μ β t ht q).mono ((vectorBrownianFiltration n).le _) le_rfl)

theorem memLp_standardSKSelectedMean (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (J : Finset (Fin n)) (q : Paper.Overlap) :
    MemLp (standardSKSelectedMean (n:=n) μ β t ht J q) 2 (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply MemLp.of_bound (measurable_standardSKSelectedMean μ β t ht J q).aestronglyMeasurable
    (‖anisotropicSelectedFieldMap J‖*Real.sqrt (n:ℝ))
  exact .of_forall fun sample=>((anisotropicSelectedFieldMap J).le_opNorm _).trans
    (mul_le_mul_of_nonneg_left (norm_vectorMeasureGradient_le μ β t ht q sample.1 _)
      (norm_nonneg _))

theorem integrable_standardSKSelectedHessianEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (J : Finset (Fin n)) (q : Paper.Overlap) :
    Integrable (standardSKSelectedHessianEnergy (n:=n) μ β t ht J q) (vectorMeasureDisorderTilt μ β t a) := by
  have hm:=memLp_standardSKSelectedMean (n:=n) μ β t a ht J q
  have hH:=memLp_vectorMeasureHessian_random_apply μ β t a ht q _ hm
  exact (hH.norm.integrable_mul hm.norm).mono' (hH.aestronglyMeasurable.inner hm.aestronglyMeasurable)
    (.of_forall fun sample=>norm_inner_le_norm _ _)

theorem integrable_standardSKSelectedCovarianceEnergy (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (J : Finset (Fin n)) (q : Paper.Overlap) :
    Integrable (standardSKSelectedCovarianceEnergy (n:=n) μ β t a ht J q) (vectorMeasureDisorderTilt μ β t a) :=
  integrable_vectorMeasureRandomCovariance μ β t a ht q _ (memLp_standardSKSelectedMean μ β t a ht J q)

end QuantitativeFollowup
