module
public import QuantitativePaper.VectorTiltedExponentialLocalization
public import QuantitativePaper.VectorGaussianLowerPropagation
public import FourPapersCommon.BoundedTimeInterval

@[expose] public section

/-! True space-time exponential moments of the product Wiener process.
The time integral is justified from a uniform Gaussian marginal bound;
no Brownian supremum estimate is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem integral_exp_disorderVectorBrownian_norm_le (K : ℝ) (r : ℝ≥0) (hr : r≤1) :
    (∫sample : VectorDisorderBrownianSample n,Real.exp (K*‖disorderVectorBrownian r sample‖)
      ∂vectorDisorderBrownianMeasure n) ≤ vectorGaussianNormLaplace n |K| := by
  have hl:=hasLaw_disorderVectorBrownianIncrement (n := n) 0 r bot_le
  have he:=hl.integral_comp (f := fun z : Field n=>Real.exp (K*‖z‖)) (by fun_prop)
  simp only [Function.comp_apply,disorderVectorBrownianIncrement,disorderVectorBrownian,
    vectorBrownian_zero,tsub_zero,sub_zero] at he
  change (∫sample : VectorDisorderBrownianSample n,Real.exp (K*‖vectorBrownian r sample.2‖)
    ∂vectorDisorderBrownianMeasure n)≤_
  rw [he]
  unfold fieldIncrementLaw
  rw [integral_map_of_stronglyMeasurable (by fun_prop) (by fun_prop)]
  unfold vectorGaussianNormLaplace
  apply integral_mono
    (by simpa only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),mul_assoc] using
      SYK.integrable_exp_mul_norm (ι := Fin n) (K*Real.sqrt (r : ℝ)))
    (SYK.integrable_exp_mul_norm (ι := Fin n) |K|)
  intro z
  dsimp only
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.exp_le_exp.mpr
  have hs : Real.sqrt (r : ℝ)≤1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show (r : ℝ)≤1 from hr)
  have hk := mul_le_mul_of_nonneg_right (le_abs_self K)
    (mul_nonneg (Real.sqrt_nonneg (r : ℝ)) (norm_nonneg z))
  have hh:=mul_le_of_le_one_right (abs_nonneg K) hs
  nlinarith [mul_le_mul_of_nonneg_right hh (norm_nonneg z)]

theorem integrable_time_exp_disorderVectorBrownian_norm (K : ℝ) :
    Integrable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      Real.exp (K*‖disorderVectorBrownian z.1 z.2‖))
      ((nonnegativeLebesgueMeasure.restrict (Ioc 0 1)).prod (vectorDisorderBrownianMeasure n)) := by
  let ν:=nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) 1)
  letI : IsFiniteMeasure ν:=⟨by simpa only [ν,Measure.restrict_apply_univ] using
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1))⟩
  have hm : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      Real.exp (K*‖disorderVectorBrownian z.1 z.2‖)):=
    Real.measurable_exp.comp ((measurable_uncurry_disorderVectorBrownian n).norm.const_mul K)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall fun r=>integrable_exp_disorderVectorBrownian_norm r K,?_⟩
  apply (integrable_const (vectorGaussianNormLaplace n |K|)).mono'
    hm.stronglyMeasurable.norm.integral_prod_right'.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_of_nonneg (integral_nonneg fun _=>norm_nonneg _)]
  simp only [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact integral_exp_disorderVectorBrownian_norm_le K r hr.2

end QuantitativePaper
