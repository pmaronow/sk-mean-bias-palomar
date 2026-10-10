module
public import QuantitativeFollowup.SupportingNativeConditionalHessianIntegralFiniteCell
public import FourPapersCommon.BoundedTimeInterval
public import FourPapersCommon.LocalItoEndpoints

@[expose] public section

/-! Native directional mean and Hessian noise energy: actual joint
measurability, continuous sample paths, and bounds independent of the
finite profile and its depth. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped NNReal ContDiff BigOperators Topology
namespace QuantitativeFollowup
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def nativeAnisotropicNoiseEnergyBound (D : AnisotropicSpinModel n) (w : Field n) : ℝ :=
  (n:ℝ)*(‖anisotropicEnergyMap D‖^2*‖anisotropicUnitInput D‖*‖anisotropicFieldInjection n w‖)^2

theorem nativeAnisotropicNoiseEnergyBound_nonneg (D : AnisotropicSpinModel n) (w : Field n) :
    0≤nativeAnisotropicNoiseEnergyBound D w := by unfold nativeAnisotropicNoiseEnergyBound;positivity

private theorem native_finite_parameter_measurable (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) :
    Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      (projIcc (0:ℝ) 1 zero_le_one (z.1:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g z.1 z.2))) := by
  have hx:=measurable_uncurry_vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1
  exact (continuous_projIcc.measurable.comp (NNReal.continuous_coe.measurable.comp measurable_fst)).prodMk
    (measurable_const.add ((anisotropicUnitInput D).continuous.measurable.comp hx))

private theorem native_finite_parameter_continuous (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r : ℝ≥0=>
      (projIcc (0:ℝ) 1 zero_le_one (r:ℝ),anisotropicDisorderInjection n g+
        anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))) :=
  (continuous_projIcc.comp NNReal.continuous_coe).prodMk
    (continuous_const.add ((anisotropicUnitInput D).continuous.comp
      (continuous_vectorAdditiveState (anisotropicWhitenedFiniteDriftData D s g) 1 0 1 sample)))

theorem measurable_uncurry_nativeAnisotropicFiniteDirectionalMean (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicFiniteDirectionalMean D s g w)) := by
  have h:=(continuous_anisotropicFiniteTailDifferential_joint D s).measurable.comp
    (native_finite_parameter_measurable D s g)
  exact ((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp h

theorem continuous_nativeAnisotropicFiniteDirectionalMean (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicFiniteDirectionalMean D s g w r sample) :=
  ((continuous_anisotropicFiniteTailDifferential_joint D s).comp
    (native_finite_parameter_continuous D s g sample)).clm_apply continuous_const

theorem norm_nativeAnisotropicFiniteDirectionalMean_le (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖nativeAnisotropicFiniteDirectionalMean D s g w r sample‖≤Real.sqrt (n:ℝ)*‖w‖ := by
  unfold nativeAnisotropicFiniteDirectionalMean
  rw [fderiv_anisotropicFiniteTailPotential_field]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
    (norm_anisotropicFiniteTailMagnetization_le D s _ _) (norm_nonneg w))

theorem measurable_uncurry_nativeAnisotropicFiniteDirectionalNoiseEnergy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n) :
    Measurable (Function.uncurry (nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w)) := by
  have h:=(continuous_anisotropicFiniteTailSecondDifferential_joint D s).measurable.comp
    (native_finite_parameter_measurable D s g)
  unfold Function.uncurry nativeAnisotropicFiniteDirectionalNoiseEnergy
  apply Finset.measurable_sum
  intro l _
  exact (((ContinuousLinearMap.apply ℝ ℝ) (anisotropicFieldInjection n w)).continuous.measurable.comp
    (((ContinuousLinearMap.apply ℝ (AnisotropicParameter n→L[ℝ]ℝ))
      (anisotropicUnitInput D (EuclideanSpace.single l 1))).continuous.measurable.comp h)).pow_const 2

theorem continuous_nativeAnisotropicFiniteDirectionalNoiseEnergy
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    Continuous (fun r=>nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample) := by
  have h:=(continuous_anisotropicFiniteTailSecondDifferential_joint D s).comp
    (native_finite_parameter_continuous D s g sample)
  exact continuous_finsetSum _ (fun l _=>((h.clm_apply continuous_const).clm_apply continuous_const).pow 2)

theorem nativeAnisotropicFiniteDirectionalNoiseEnergy_le
    (D : AnisotropicSpinModel n) (s : RSBScheme k) (g : AnisotropicDisorder n) (w : Field n)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    nativeAnisotropicFiniteDirectionalNoiseEnergy D s g w r sample≤nativeAnisotropicNoiseEnergyBound D w := by
  let T:=fderiv ℝ (fderiv ℝ (anisotropicFiniteTailPotential D s
    (projIcc (0:ℝ) 1 zero_le_one r)))
      (anisotropicDisorderInjection n g+anisotropicUnitInput D (anisotropicWhitenedFiniteState D s g r sample))
  let V:=anisotropicFieldInjection n w
  have hT : ‖T‖≤‖anisotropicEnergyMap D‖^2:=norm_anisotropicFiniteTailSecondDifferential_le D s _ _
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

end QuantitativeFollowup
