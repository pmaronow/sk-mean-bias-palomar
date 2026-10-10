module
public import QuantitativeFollowup.AnisotropicOuterWeightConvergence
public import QuantitativeFollowup.AnisotropicMeasureDrift
public import QuantitativeFollowup.AnisotropicFiniteWienerRealization

@[expose] public section

/-! Honest density and bounded-observable limits on the common independent
anisotropic disorder/Wiener space. Normalization and domination are derived
from the actual finite and arbitrary-profile potentials. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter FourPapersCommon QuantitativePaper
open scoped Topology NNReal ENNReal
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1000000

def anisotropicBaseWienerLaw (n : ℕ) : Measure (AnisotropicDisorderBrownianSample n) :=
  (anisotropicDisorderLaw n).prod (vectorBrownianMeasure n)

instance anisotropicBaseWienerLaw_probability (n : ℕ) :
    IsProbabilityMeasure (anisotropicBaseWienerLaw n) := by
  unfold anisotropicBaseWienerLaw
  infer_instance

theorem measurable_anisotropicDyadicOuterWeight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) :
    Measurable (anisotropicDyadicOuterWeight D μ a j) := by
  have hp : Continuous (anisotropicDyadicPotential D μ j) :=
    (contDiff_anisotropicFinitePotential D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (vectorDyadicIndex j+3)).continuous
  exact (Real.measurable_exp.comp
    ((hp.measurable.comp (anisotropicDisorderInjection n).continuous.measurable).const_mul a)).div_const _

theorem measurable_anisotropicMeasureOuterWeight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) : Measurable (anisotropicMeasureOuterWeight D μ a) :=
  (Real.measurable_exp.comp (((continuous_anisotropicMeasurePotential D μ).measurable.comp
    (anisotropicDisorderInjection n).continuous.measurable).const_mul a)).div_const _

theorem anisotropicMeasureOuterWeight_nonneg (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (g : AnisotropicDisorder n) :
    0 ≤ anisotropicMeasureOuterWeight D μ a g :=
  (div_pos (Real.exp_pos _) (anisotropicMeasureOuterPartition_pos D μ a)).le

theorem integrable_anisotropicMeasureOuterWeight (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (anisotropicMeasureOuterWeight D μ a) (anisotropicDisorderLaw n) :=
  (integrable_exp_anisotropicMeasurePotential D μ a).div_const _

theorem anisotropicMeasureSampleLaw_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    anisotropicMeasureSampleLaw D μ a=(anisotropicBaseWienerLaw n).withDensity
      (fun sample => ENNReal.ofReal (anisotropicMeasureOuterWeight D μ a sample.1)) := by
  rw [anisotropicMeasureSampleLaw,anisotropicMeasureOuterLaw_density]
  change ((anisotropicDisorderLaw n).withDensity
    (fun g => ENNReal.ofReal (anisotropicMeasureOuterWeight D μ a g))).prod
      (vectorBrownianMeasure n)=_
  exact prod_withDensity_left
    (ENNReal.measurable_ofReal.comp (measurable_anisotropicMeasureOuterWeight D μ a))

theorem integral_anisotropicMeasureSampleLaw_weighted (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (F : AnisotropicDisorderBrownianSample n → ℝ) :
    (∫ sample,F sample ∂anisotropicMeasureSampleLaw D μ a)=
      ∫ sample,anisotropicMeasureOuterWeight D μ a sample.1*F sample ∂anisotropicBaseWienerLaw n := by
  rw [anisotropicMeasureSampleLaw_density]
  have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      ENNReal.ofReal (anisotropicMeasureOuterWeight D μ a sample.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_anisotropicMeasureOuterWeight D μ a).comp measurable_fst)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  simp only [ENNReal.toReal_ofReal (anisotropicMeasureOuterWeight_nonneg D μ a _),smul_eq_mul]

theorem anisotropicDyadicWienerSampleLaw_density (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) :
    anisotropicFiniteWienerSampleLaw D (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a=
      (anisotropicBaseWienerLaw n).withDensity
        (fun sample => ENNReal.ofReal (anisotropicDyadicOuterWeight D μ a j sample.1)) := by
  change ((anisotropicDisorderLaw n).withDensity
    (fun g => ENNReal.ofReal (anisotropicDyadicOuterWeight D μ a j g))).prod
      (vectorBrownianMeasure n)=_
  exact prod_withDensity_left
    (ENNReal.measurable_ofReal.comp (measurable_anisotropicDyadicOuterWeight D μ a j))

theorem integral_anisotropicDyadicWienerSampleLaw_weighted (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (j : ℕ) (F : AnisotropicDisorderBrownianSample n → ℝ) :
    (∫ sample,F sample ∂anisotropicFiniteWienerSampleLaw D
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) a)=
      ∫ sample,anisotropicDyadicOuterWeight D μ a j sample.1*F sample ∂anisotropicBaseWienerLaw n := by
  rw [anisotropicDyadicWienerSampleLaw_density]
  have hm : Measurable (fun sample : AnisotropicDisorderBrownianSample n =>
      ENNReal.ofReal (anisotropicDyadicOuterWeight D μ a j sample.1)) :=
    ENNReal.measurable_ofReal.comp ((measurable_anisotropicDyadicOuterWeight D μ a j).comp measurable_fst)
  rw [integral_withDensity_eq_integral_toReal_smul hm
    (.of_forall fun _ => ENNReal.ofReal_lt_top) F]
  apply integral_congr_ae
  exact .of_forall fun sample => by
    change (ENNReal.ofReal (anisotropicDyadicOuterWeight D μ a j sample.1)).toReal • F sample=
      anisotropicDyadicOuterWeight D μ a j sample.1*F sample
    rw [ENNReal.toReal_ofReal (show 0 ≤ anisotropicDyadicOuterWeight D μ a j sample.1 from
      (div_pos (Real.exp_pos _) (anisotropicDyadicOuterPartition_pos D μ a j)).le),smul_eq_mul]

theorem tendsto_integral_anisotropicDyadicOuterWeight_abs_sub (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Tendsto (fun j => ∫ sample : AnisotropicDisorderBrownianSample n,
      |anisotropicDyadicOuterWeight D μ a j sample.1-anisotropicMeasureOuterWeight D μ a sample.1|
        ∂anisotropicBaseWienerLaw n) atTop (𝓝 0) := by
  let B := fun sample : AnisotropicDisorderBrownianSample n =>
    2*anisotropicOuterExponentialEnvelope D μ a sample.1/anisotropicMeasureOuterPartition D μ a+
      ‖anisotropicMeasureOuterWeight D μ a sample.1‖
  have hB : Integrable B (anisotropicBaseWienerLaw n) :=
    (((integrable_anisotropicOuterExponentialEnvelope D μ a).const_mul 2).div_const _
      |>.comp_fst (vectorBrownianMeasure n)).add
      ((integrable_anisotropicMeasureOuterWeight D μ a).norm.comp_fst (vectorBrownianMeasure n))
  have hconv : Tendsto (fun j => ∫ sample : AnisotropicDisorderBrownianSample n,
      |anisotropicDyadicOuterWeight D μ a j sample.1-anisotropicMeasureOuterWeight D μ a sample.1|
        ∂anisotropicBaseWienerLaw n) atTop (𝓝 (∫ _sample, (0 : ℝ) ∂anisotropicBaseWienerLaw n)) := by
    apply tendsto_integral_filter_of_dominated_convergence B
    · exact .of_forall fun j =>
        (((measurable_anisotropicDyadicOuterWeight D μ a j).comp measurable_fst).sub
          ((measurable_anisotropicMeasureOuterWeight D μ a).comp measurable_fst)).abs.aestronglyMeasurable
    · filter_upwards [anisotropicDyadicOuterWeight_eventual_bound D μ a] with j hj
      exact .of_forall fun sample => by
        rw [Real.norm_eq_abs,abs_abs]
        exact (abs_sub _ _).trans (add_le_add (by simpa only [Real.norm_eq_abs] using hj sample.1) le_rfl)
    · exact hB
    · exact .of_forall fun sample => by
        simpa only [sub_self,abs_zero] using
          ((tendsto_anisotropicDyadicOuterWeight D μ a sample.1).sub_const
            (anisotropicMeasureOuterWeight D μ a sample.1)).abs
  simpa only [integral_zero] using hconv

end QuantitativeFollowup
