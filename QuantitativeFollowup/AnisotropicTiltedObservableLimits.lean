module
public import QuantitativeFollowup.AnisotropicOuterDensityLimits
public import FourPapersCommon.ExpWeightedConvergence

@[expose] public section

/-! Actual bounded moments and variances pass from the finite anisotropic
Wiener laws to the arbitrary-profile law. The varying disorder density is
the genuine normalized exponential tilt of the constructed potential. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon QuantitativePaper
open scoped NNReal ENNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem tendsto_integral_anisotropicDyadicTilt_bounded (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (Fj : ℕ→AnisotropicDisorderBrownianSample n→ℝ)
    (F : AnisotropicDisorderBrownianSample n→ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hFj : ∀j,Measurable (Fj j)) (hB : ∀j sample,‖Fj j sample‖ ≤ C)
    (hF : ∀ᵐ sample ∂anisotropicBaseWienerLaw n,
      Tendsto (fun j => Fj j sample) atTop (𝓝 (F sample))) :
    Tendsto (fun j => ∫sample,Fj j sample ∂anisotropicFiniteWienerSampleLaw D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a) atTop
      (𝓝 (∫sample,F sample ∂anisotropicMeasureSampleLaw D μ a)) := by
  have hε : Tendsto (fun j : ℕ =>
      (4*anisotropicProfileStabilityConstant D)*(1/2 : ℝ)^j) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2)
        (by norm_num : (1/2 : ℝ)<1)).const_mul (4*anisotropicProfileStabilityConstant D)
  have he := tendsto_integral_exp_mul_of_uniform_error
    (fun sample : AnisotropicDisorderBrownianSample n =>
      anisotropicMeasurePotential D μ (anisotropicDisorderInjection n sample.1))
    (fun j sample => anisotropicDyadicPotential D μ j (anisotropicDisorderInjection n sample.1))
    Fj F a C hC _ hε
    (fun j => ((contDiff_anisotropicFinitePotential D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) (vectorDyadicIndex j+3)).continuous.measurable).comp
        ((anisotropicDisorderInjection n).continuous.measurable.comp measurable_fst))
    hFj ((integrable_exp_anisotropicMeasurePotential D μ a).comp_fst (vectorBrownianMeasure n))
    (fun j sample => anisotropicDyadicPotential_limit_abs_sub_le D μ j
      (anisotropicDisorderInjection n sample.1)) hB hF
  simp only [integral_anisotropicDyadicWienerSampleLaw_weighted,
    integral_anisotropicMeasureSampleLaw_weighted]
  simp_rw [anisotropicDyadicOuterWeight,anisotropicMeasureOuterWeight,div_mul_eq_mul_div]
  simp only [integral_div]
  exact he.div (tendsto_anisotropicDyadicOuterPartition D μ a)
    (anisotropicMeasureOuterPartition_pos D μ a).ne'

theorem tendsto_variance_anisotropicDyadicTilt_bounded (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (Fj : ℕ→AnisotropicDisorderBrownianSample n→ℝ)
    (F : AnisotropicDisorderBrownianSample n→ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hFj : ∀j,Measurable (Fj j)) (hFm : Measurable F)
    (hB : ∀j sample,‖Fj j sample‖ ≤ C) (hB0 : ∀sample,‖F sample‖ ≤ C)
    (hF : ∀ᵐ sample ∂anisotropicBaseWienerLaw n,
      Tendsto (fun j => Fj j sample) atTop (𝓝 (F sample))) :
    Tendsto (fun j => variance (Fj j) (anisotropicFiniteWienerSampleLaw D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a)) atTop
      (𝓝 (variance F (anisotropicMeasureSampleLaw D μ a))) := by
  have hj (j : ℕ) : MemLp (Fj j) 2 (anisotropicFiniteWienerSampleLaw D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a) :=
    MemLp.of_bound (hFj j).aestronglyMeasurable C (.of_forall (hB j))
  have h0 : MemLp F 2 (anisotropicMeasureSampleLaw D μ a) :=
    MemLp.of_bound hFm.aestronglyMeasurable C (.of_forall hB0)
  simp_rw [variance_eq_sub (hj _),variance_eq_sub h0]
  have hmean := tendsto_integral_anisotropicDyadicTilt_bounded D μ a Fj F C hC hFj hB hF
  have hsquare := tendsto_integral_anisotropicDyadicTilt_bounded D μ a
    (fun j sample => (Fj j sample)^2) (fun sample => (F sample)^2) (C^2) (sq_nonneg _)
    (fun j => (hFj j).pow_const 2)
    (fun j sample => by simpa only [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (hB j sample) 2)
    (hF.mono fun sample hs => hs.pow 2)
  exact hsquare.sub (hmean.pow 2)

end QuantitativeFollowup
