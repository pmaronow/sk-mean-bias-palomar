module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralFiniteCompensation
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralEnergyRegularity

@[expose] public section

/-! The literal native finite Hessian process is jointly measurable and
has continuous paths with a profile-independent bound. Its weighted
expectation is continuous without an expectation-continuity premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

private theorem native_hessian_parameter_measurable (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      (projIcc (0:ℝ) 1 zero_le_one (z.1:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g z.1 z.2))) := by
  have hx:=measurable_uncurry_vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1
  exact (continuous_projIcc.measurable.comp (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
    (measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp hx))

theorem measurable_uncurry_nativeAnisotropicFiniteDirectionalHessian (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicFiniteDirectionalHessian D s g w)) := by
  have h:=(continuous_anisotropicFiniteTailSecondDifferential_joint D s).measurable.comp
    (native_hessian_parameter_measurable D s g)
  exact ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicFieldInjection n w)).continuous.measurable.comp h)

theorem continuous_nativeAnisotropicFiniteDirectionalHessian (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicFiniteDirectionalHessian D s g w r sample) := by
  have hp : Continuous (fun r : ℝ≥0=>
      (projIcc (0:ℝ) 1 zero_le_one (r:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))) :=
    (continuous_projIcc.comp NNReal.continuous_coe).prodMk
      (continuous_const.add ((anisotropicUnitInput D).continuous.comp
        (continuous_vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1 sample)))
  exact (((continuous_anisotropicFiniteTailSecondDifferential_joint D s).comp hp).clm_apply
    continuous_const).clm_apply continuous_const

theorem norm_nativeAnisotropicFiniteDirectionalHessian_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖nativeAnisotropicFiniteDirectionalHessian D s g w r sample‖≤
      ‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2 := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s
    (projIcc (0:ℝ) 1 zero_le_one r)))
      (anisotropicDisorderInjection n g+anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))
  let V:=anisotropicFieldInjection n w
  have hT : ‖T‖≤‖anisotropicEnergyMap D‖^2:=norm_anisotropicFiniteTailSecondDifferential_le D s _ _
  change ‖T V V‖≤_
  calc
    _≤‖T‖*‖V‖*‖V‖:=((T V).le_opNorm V).trans
      (mul_le_mul_of_nonneg_right (T.le_opNorm V) (norm_nonneg V))
    _≤‖anisotropicEnergyMap D‖^2*‖V‖*‖V‖:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hT (norm_nonneg V)) (norm_nonneg V)
    _=‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2:=by dsimp only [V];ring

def nativeFiniteHessianExpectation (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (Z : VectorDisorderBrownianSample n→ℝ) (r : ℝ) : ℝ :=
  ∫sample,Z sample*nativeAnisotropicFiniteDirectionalHessian D s g w r.toNNReal sample
    ∂vectorDisorderBrownianMeasure n

theorem integrable_nativeFinite_weighted_hessian (D : AnisotropicSpinModel n) (s : RSBScheme k)
    (g : AnisotropicDisorder n) (w : Field n) (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable Z) (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (r : ℝ≥0) :
    Integrable (fun sample=>Z sample*nativeAnisotropicFiniteDirectionalHessian D s g w r sample)
      (vectorDisorderBrownianMeasure n) := by
  apply (integrable_const ((C:ℝ)*(‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2))).mono'
    (hZ.mul (measurable_uncurry_nativeAnisotropicFiniteDirectionalHessian D s g w).of_uncurry_left).aestronglyMeasurable
  exact .of_forall fun sample=>by
    change ‖Z sample*nativeAnisotropicFiniteDirectionalHessian D s g w r sample‖≤_
    rw [norm_mul]
    exact mul_le_mul (hC sample) (norm_nativeAnisotropicFiniteDirectionalHessian_le D s g w r sample)
      (norm_nonneg _) C.coe_nonneg

theorem continuous_nativeFiniteHessianExpectation (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Continuous (nativeFiniteHessianExpectation D s g w Z) := by
  apply continuous_of_dominated (bound:=fun _ : VectorDisorderBrownianSample n=>
    (C:ℝ)*(‖anisotropicEnergyMap D‖^2*‖anisotropicFieldInjection n w‖^2))
  · intro r
    exact (integrable_nativeFinite_weighted_hessian D s g w Z hZ C hC r.toNNReal).aestronglyMeasurable
  · intro r
    exact .of_forall fun sample=>by
      rw [norm_mul]
      exact mul_le_mul (hC sample) (norm_nativeAnisotropicFiniteDirectionalHessian_le D s g w _ sample)
        (norm_nonneg _) C.coe_nonneg
  · exact integrable_const _
  · exact .of_forall fun sample=>continuous_const.mul
      ((continuous_nativeAnisotropicFiniteDirectionalHessian D s g w sample).comp continuous_real_toNNReal)

end QuantitativeFollowup
