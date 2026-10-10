module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralHessianClosed
public import QuantitativeFollowup.AnisotropicWhitenedStateConvergence

@[expose] public section

/-! Actual arbitrary-profile directional mean, Hessian and noise energy on
 the genuine same-driver white Picard state. Regularity and bounds are
 proved directly from the constructed process and its actual spatial jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def nativeAnisotropicMeasureWhiteState (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) : ℝ≥0→VectorDisorderBrownianSample n→Field n :=
  vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1

def nativeAnisotropicMeasureDirectionalMean (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (anisotropicMeasureTailPotential D μ (projIcc (0:ℝ) 1 zero_le_one r))
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (nativeAnisotropicMeasureWhiteState D μ g r sample)) (anisotropicFieldInjection n w)

def nativeAnisotropicMeasureDirectionalHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ (projIcc (0:ℝ) 1 zero_le_one r)))
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (nativeAnisotropicMeasureWhiteState D μ g r sample))
      (anisotropicFieldInjection n w) (anisotropicFieldInjection n w)

def nativeAnisotropicMeasureDirectionalNoiseEnergy (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑l : Fin n,(fderiv ℝ (fderiv ℝ
      (anisotropicMeasureTailPotential D μ (projIcc (0:ℝ) 1 zero_le_one r)))
    (anisotropicDisorderInjection n g+anisotropicUnitInput D
      (nativeAnisotropicMeasureWhiteState D μ g r sample))
    (anisotropicUnitInput D (EuclideanSpace.single l 1)) (anisotropicFieldInjection n w))^2

theorem nativeAnisotropicMeasureDirectionalNoiseEnergy_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    0≤nativeAnisotropicMeasureDirectionalNoiseEnergy D μ g w r sample :=
  Finset.sum_nonneg fun _ _=>sq_nonneg _

private theorem native_measure_parameter_measurable (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      (projIcc (0:ℝ) 1 zero_le_one (z.1:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (nativeAnisotropicMeasureWhiteState D μ g z.1 z.2))) := by
  have hx:=measurable_uncurry_vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1
  exact (continuous_projIcc.measurable.comp (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
    (measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp hx))

private theorem native_measure_parameter_continuous (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>
      (projIcc (0:ℝ) 1 zero_le_one (r:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (nativeAnisotropicMeasureWhiteState D μ g r sample))) :=
  (continuous_projIcc.comp NNReal.continuous_coe).prodMk
    (continuous_const.add ((anisotropicUnitInput D).continuous.comp
      (continuous_vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1 sample)))

theorem measurable_uncurry_nativeAnisotropicMeasureDirectionalMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicMeasureDirectionalMean D μ g w)) := by
  have h:=(continuous_anisotropicMeasureTailDifferential_joint D μ).measurable.comp
    (native_measure_parameter_measurable D μ g)
  exact ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp h

theorem continuous_nativeAnisotropicMeasureDirectionalMean (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicMeasureDirectionalMean D μ g w r sample) :=
  ((continuous_anisotropicMeasureTailDifferential_joint D μ).comp
    (native_measure_parameter_continuous D μ g sample)).clm_apply continuous_const

theorem norm_nativeAnisotropicMeasureDirectionalMean_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖nativeAnisotropicMeasureDirectionalMean D μ g w r sample‖≤Real.sqrt (n:ℝ)*‖w‖ := by
  unfold nativeAnisotropicMeasureDirectionalMean
  rw [fderiv_anisotropicMeasureTailPotential_field]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_anisotropicMeasureTailMagnetization_le D μ _ _) (norm_nonneg w))

theorem measurable_uncurry_nativeAnisotropicMeasureDirectionalNoiseEnergy
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicMeasureDirectionalNoiseEnergy D μ g w)) := by
  have h:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    (native_measure_parameter_measurable D μ g)
  unfold Function.uncurry nativeAnisotropicMeasureDirectionalNoiseEnergy
  apply Finset.measurable_sum
  intro l _
  exact (((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicUnitInput D (EuclideanSpace.single l 1))).continuous.measurable.comp h)).pow_const 2

theorem continuous_nativeAnisotropicMeasureDirectionalNoiseEnergy
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicMeasureDirectionalNoiseEnergy D μ g w r sample) := by
  have h:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).comp
    (native_measure_parameter_continuous D μ g sample)
  exact continuous_finsetSum _ (fun l _=>((h.clm_apply continuous_const).clm_apply continuous_const).pow 2)

theorem nativeAnisotropicMeasureDirectionalNoiseEnergy_le
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    nativeAnisotropicMeasureDirectionalNoiseEnergy D μ g w r sample≤nativeAnisotropicNoiseEnergyBound D w := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ
    (projIcc (0:ℝ) 1 zero_le_one r)))
      (anisotropicDisorderInjection n g+anisotropicUnitInput D (nativeAnisotropicMeasureWhiteState D μ g r sample))
  let V:=anisotropicFieldInjection n w
  have hT : ‖T‖≤‖anisotropicEnergyMap D‖^2:=norm_anisotropicMeasureTailSecondDifferential_le D μ _ _
  have hb (l : Fin n) : ‖T (anisotropicUnitInput D (EuclideanSpace.single l 1)) V‖≤
      ‖anisotropicEnergyMap D‖^2*‖anisotropicUnitInput D‖*‖V‖ := by
    have ha : ‖anisotropicUnitInput D (EuclideanSpace.single l 1)‖≤‖anisotropicUnitInput D‖:=by
      simpa only [EuclideanSpace.norm_single,norm_one,mul_one] using
        (anisotropicUnitInput D).le_opNorm (EuclideanSpace.single l 1)
    calc
      _≤‖T‖*‖anisotropicUnitInput D (EuclideanSpace.single l 1)‖*‖V‖ :=
        ((T _).le_opNorm V).trans (mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg V))
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul hT ha (norm_nonneg _) (sq_nonneg _)) (norm_nonneg V)
  change (∑l : Fin n,(T (anisotropicUnitInput D (EuclideanSpace.single l 1)) V)^2)≤_
  calc
    _≤∑_ : Fin n,(‖anisotropicEnergyMap D‖^2*‖anisotropicUnitInput D‖*‖V‖)^2:=
      Finset.sum_le_sum fun l _=>by
        simpa only [Real.norm_eq_abs,sq_abs] using
          pow_le_pow_left₀ (norm_nonneg _) (hb l) 2
    _=nativeAnisotropicNoiseEnergyBound D w:=by simp [nativeAnisotropicNoiseEnergyBound,V]

theorem measurable_uncurry_nativeAnisotropicMeasureDirectionalHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicMeasureDirectionalHessian D μ g w)) := by
  have h:=(continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp
    (native_measure_parameter_measurable D μ g)
  exact ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicFieldInjection n w)).continuous.measurable.comp h)

theorem continuous_nativeAnisotropicMeasureDirectionalHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicMeasureDirectionalHessian D μ g w r sample) := by
  have hp : Continuous (fun r : ℝ≥0=>
      (projIcc (0:ℝ) 1 zero_le_one (r:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (nativeAnisotropicMeasureWhiteState D μ g r sample))) :=
    (continuous_projIcc.comp NNReal.continuous_coe).prodMk
      (continuous_const.add ((anisotropicUnitInput D).continuous.comp
        (continuous_vectorAdditiveState (anisotropicWhitenedDriftData D μ g) 1 0 1 sample)))
  exact (((continuous_anisotropicMeasureTailSecondDifferential_joint D μ).comp hp).clm_apply
    continuous_const).clm_apply continuous_const

theorem norm_nativeAnisotropicMeasureDirectionalHessian_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖nativeAnisotropicMeasureDirectionalHessian D μ g w r sample‖≤
      ‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2 := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicMeasureTailPotential D μ
    (projIcc (0:ℝ) 1 zero_le_one r)))
      (anisotropicDisorderInjection n g+anisotropicUnitInput D (nativeAnisotropicMeasureWhiteState D μ g r sample))
  let V:=anisotropicFieldInjection n w
  have hT : ‖T‖≤‖anisotropicEnergyMap D‖^2:=norm_anisotropicMeasureTailSecondDifferential_le D μ _ _
  change ‖T V V‖≤_
  calc
    _≤‖T‖*‖V‖*‖V‖:=((T V).le_opNorm V).trans
      (mul_le_mul_of_nonneg_right (T.le_opNorm V) (norm_nonneg V))
    _≤‖anisotropicEnergyMap D‖^2*‖V‖*‖V‖:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT (norm_nonneg V)) (norm_nonneg V)
    _=‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2:=by dsimp only [V];ring


end QuantitativeFollowup
