module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralMeasureRegularity
public import QuantitativeFollowup.AnisotropicNativeSpinConditionals
public import QuantitativeFollowup.AnisotropicProcessCovarianceEnergy

@[expose] public section

/-! Literal directional field Hessian and H-Lambda-H noise energy on the
actual native anisotropic diffusion, with genuine past adaptation and
profile-independent bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def nativeAnisotropicProcessDirectionalMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (anisotropicMeasureTailPotential D μ q) (anisotropicProcessParameter D μ q sample)
    (anisotropicFieldInjection n w)

def nativeAnisotropicProcessDirectionalHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
    (anisotropicProcessParameter D μ q sample) (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)

def nativeAnisotropicProcessDirectionalNoiseEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) : ℝ :=
  ∑l : Fin n,(fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ q))
    (anisotropicProcessParameter D μ q sample)
    (anisotropicUnitInput D (EuclideanSpace.single l 1)) (anisotropicFieldInjection n w))^2

private theorem native_process_parameter_eq_white (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    anisotropicProcessParameter D μ q (g,sample.2)=
      anisotropicDisorderInjection n g+anisotropicUnitInput D
        (nativeAnisotropicMeasureWhiteState D μ g (q:ℝ).toNNReal sample) := by
  have hq : (q:ℝ).toNNReal≤1:=by simpa using Real.toNNReal_le_toNNReal q.property.2
  have hh:=anisotropicMeasureState_eq_whitenedPicard D μ g sample (q:ℝ).toNNReal hq
  rw [Real.coe_toNNReal _ q.property.1] at hh
  unfold anisotropicProcessParameter
  rw [hh]
  rfl

theorem nativeAnisotropicProcessDirectionalMean_eq_white (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    nativeAnisotropicProcessDirectionalMean D μ w q (g,sample.2)=
      nativeAnisotropicMeasureDirectionalMean D μ g w (q:ℝ).toNNReal sample := by
  unfold nativeAnisotropicProcessDirectionalMean nativeAnisotropicMeasureDirectionalMean
  rw [Real.coe_toNNReal _ q.property.1,projIcc_of_mem zero_le_one q.property,
    native_process_parameter_eq_white]

theorem nativeAnisotropicProcessDirectionalHessian_eq_white (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    nativeAnisotropicProcessDirectionalHessian D μ w q (g,sample.2)=
      nativeAnisotropicMeasureDirectionalHessian D μ g w (q:ℝ).toNNReal sample := by
  unfold nativeAnisotropicProcessDirectionalHessian nativeAnisotropicMeasureDirectionalHessian
  rw [Real.coe_toNNReal _ q.property.1,projIcc_of_mem zero_le_one q.property,
    native_process_parameter_eq_white]

theorem nativeAnisotropicProcessDirectionalNoiseEnergy_eq_white (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) (q : Paper.Overlap)
    (sample : VectorDisorderBrownianSample n) :
    nativeAnisotropicProcessDirectionalNoiseEnergy D μ w q (g,sample.2)=
      nativeAnisotropicMeasureDirectionalNoiseEnergy D μ g w (q:ℝ).toNNReal sample := by
  unfold nativeAnisotropicProcessDirectionalNoiseEnergy nativeAnisotropicMeasureDirectionalNoiseEnergy
  rw [Real.coe_toNNReal _ q.property.1,projIcc_of_mem zero_le_one q.property,
    native_process_parameter_eq_white]

theorem nativeAnisotropicProcessDirectionalMean_eq_inner (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (q : Paper.Overlap)
    (sample : AnisotropicDisorderBrownianSample n) :
    nativeAnisotropicProcessDirectionalMean D μ w q sample=
      inner ℝ (anisotropicProcessMagnetization D μ q sample) w :=
  fderiv_anisotropicMeasureTailPotential_field D μ q _ w

private theorem native_process_differential_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      fderiv ℝ (anisotropicMeasureTailPotential D μ z.1) (anisotropicProcessParameter D μ z.1 z.2)) := by
  have hP : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (z.1,anisotropicProcessParameter D μ z.1 z.2)):=
    measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ)
  have h:=(continuous_anisotropicMeasureTailDifferential_joint D μ).measurable.comp hP
  dsimp only [Function.comp_def] at h
  exact h

private theorem native_process_secondDifferential_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ z.1))
        (anisotropicProcessParameter D μ z.1 z.2)) := by
  have hP : Measurable (fun z : Paper.Overlap×AnisotropicDisorderBrownianSample n=>
      (z.1,anisotropicProcessParameter D μ z.1 z.2)):=
    measurable_fst.prodMk (measurable_uncurry_anisotropicProcessParameter D μ)
  have h:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp hP
  dsimp only [Function.comp_def] at h
  exact h

private theorem native_process_parameter_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun q : Paper.Overlap=>(q,anisotropicProcessParameter D μ q sample)) :=
  continuous_id.prodMk (continuous_const.add ((anisotropicFieldInjection n).continuous.comp
    ((continuous_anisotropicMeasureState D μ sample).comp continuous_subtype_val)))

theorem measurable_uncurry_nativeAnisotropicProcessDirectionalMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicProcessDirectionalMean D μ w)) :=
  ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (native_process_differential_measurable D μ)

theorem measurable_uncurry_nativeAnisotropicProcessDirectionalHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicProcessDirectionalHessian D μ w)) :=
  ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicFieldInjection n w)).continuous.measurable.comp (native_process_secondDifferential_measurable D μ))

theorem measurable_uncurry_nativeAnisotropicProcessDirectionalNoiseEnergy (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicProcessDirectionalNoiseEnergy D μ w)) := by
  unfold Function.uncurry nativeAnisotropicProcessDirectionalNoiseEnergy
  apply Finset.measurable_sum
  intro l _
  exact
    (((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
      (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
        (anisotropicUnitInput D (EuclideanSpace.single l 1))).continuous.measurable.comp
          (native_process_secondDifferential_measurable D μ))).pow_const 2

theorem continuous_nativeAnisotropicProcessDirectionalHessian_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun q=>nativeAnisotropicProcessDirectionalHessian D μ w q sample) :=
  (((continuous_anisotropicMeasureTailSecondDifferential_joint D μ).comp
    (native_process_parameter_continuous D μ sample)).clm_apply continuous_const).clm_apply continuous_const

theorem continuous_nativeAnisotropicProcessDirectionalNoiseEnergy_time (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (sample : AnisotropicDisorderBrownianSample n) :
    Continuous (fun q=>nativeAnisotropicProcessDirectionalNoiseEnergy D μ w q sample) :=
  continuous_finsetSum _ (fun l _=>((((continuous_anisotropicMeasureTailSecondDifferential_joint D μ).comp
    (native_process_parameter_continuous D μ sample)).clm_apply continuous_const).clm_apply continuous_const).pow 2)

theorem norm_nativeAnisotropicProcessDirectionalMean_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖nativeAnisotropicProcessDirectionalMean D μ w q sample‖≤Real.sqrt (n:ℝ)*‖w‖ := by
  rw [nativeAnisotropicProcessDirectionalMean_eq_white D μ sample.1 w q ((0,0),sample.2)]
  exact norm_nativeAnisotropicMeasureDirectionalMean_le D μ sample.1 w _ _

theorem norm_nativeAnisotropicProcessDirectionalHessian_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    ‖nativeAnisotropicProcessDirectionalHessian D μ w q sample‖≤
      ‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2 := by
  rw [nativeAnisotropicProcessDirectionalHessian_eq_white D μ sample.1 w q ((0,0),sample.2)]
  exact norm_nativeAnisotropicMeasureDirectionalHessian_le D μ sample.1 w _ _

theorem nativeAnisotropicProcessDirectionalNoiseEnergy_nonneg_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (q : Paper.Overlap) (sample : AnisotropicDisorderBrownianSample n) :
    0≤nativeAnisotropicProcessDirectionalNoiseEnergy D μ w q sample ∧
      nativeAnisotropicProcessDirectionalNoiseEnergy D μ w q sample≤nativeAnisotropicNoiseEnergyBound D w := by
  rw [nativeAnisotropicProcessDirectionalNoiseEnergy_eq_white D μ sample.1 w q ((0,0),sample.2)]
  exact ⟨nativeAnisotropicMeasureDirectionalNoiseEnergy_nonneg D μ sample.1 w _ _,
    nativeAnisotropicMeasureDirectionalNoiseEnergy_le D μ sample.1 w _ _⟩

theorem adapted_nativeAnisotropicProcessDirectionalHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (w : Field n) (q : Paper.Overlap) :
    Measurable[anisotropicBrownianFiltration n (q:ℝ).toNNReal]
      (nativeAnisotropicProcessDirectionalHessian D μ w q) := by
  have h:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    ((measurable_const (a:=q)).prodMk (adapted_anisotropicProcessParameter D μ q))
  exact ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicFieldInjection n w)).continuous.measurable.comp h)

end QuantitativeFollowup
