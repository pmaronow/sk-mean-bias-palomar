module
public import QuantitativePaper.VectorHeatScaleDerivative
public import FourPapersCommon.VectorGaussianQuadratic

@[expose] public section

/-! Actual first and second spatial derivatives of vector Gaussian heat
integrals, proved by dominated differentiation. The exponential-growth datum
discharges all derivative integrability and commutation requirements. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem VectorHeatDatum.jet_bound {F : Field n → ℝ} (d : VectorHeatDatum F)
    (j : ℕ) (hj : j ≤ 2) (x : Field n) :
    ‖iteratedFDeriv ℝ j F x‖ ≤ d.growthBound*Real.exp (d.rate*‖x‖) := by
  interval_cases j
  · simpa only [norm_iteratedFDeriv_zero] using d.value_bound x
  · simpa only [norm_iteratedFDeriv_one] using d.first_bound x
  · simpa only [vectorHessian_norm_eq] using d.second_bound x

theorem VectorHeatDatum.spatial_integral_inputs {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) :
    (∀ z,ContDiff ℝ 2 (fun x=>F (fieldShift v x z))) ∧
    (∀ j,j ≤ 2 → ∀ x,AEStronglyMeasurable
      (fun z=>iteratedFDeriv ℝ j (fun y=>F (fieldShift v y z)) x) (fieldGaussian n)) ∧
    (∀ x,∃ s∈𝓝 x,∃ B : ℕ → Field n → ℝ,
      (∀ j,j ≤ 2 → Integrable (B j) (fieldGaussian n)) ∧
      ∀ j,j ≤ 2 → ∀ y∈s,∀ z,
        ‖iteratedFDeriv ℝ j (fun u=>F (fieldShift v u z)) y‖ ≤ B j z) := by
  refine ⟨fun z=>d.regularity.comp (by unfold fieldShift;fun_prop),?_,?_⟩
  · intro j hj x
    simp only [fieldShift,iteratedFDeriv_comp_add_right]
    exact ((d.regularity.continuous_iteratedFDeriv (by exact_mod_cast hj)).comp
      (continuous_const.add (continuous_id.const_smul (Real.sqrt v)))).aestronglyMeasurable
  · intro x
    let B : ℕ → Field n → ℝ := fun _ z=>d.growthBound*Real.exp (d.rate*(‖x‖+1))*
      Real.exp ((d.rate*Real.sqrt v)*‖z‖)
    refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),B,?_,?_⟩
    · intro _ _
      exact (SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*Real.sqrt v)).const_mul _
    · intro j hj y hy z
      have hxy : ‖y-x‖ < 1 := by simpa only [Metric.mem_ball,dist_eq_norm] using hy
      have hny : ‖y‖ ≤ ‖x‖+1 := by
        have hh := norm_add_le x (y-x)
        rw [add_sub_cancel] at hh
        exact hh.trans (add_le_add (le_refl _) hxy.le)
      have hn : ‖y+Real.sqrt v • z‖ ≤ ‖x‖+1+Real.sqrt v*‖z‖ := by
        have hh := norm_add_le y (Real.sqrt v • z)
        simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
        exact hh.trans (add_le_add hny le_rfl)
      simp only [fieldShift,iteratedFDeriv_comp_add_right]
      apply (d.jet_bound j hj _).trans
      have hh := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn d.rate.coe_nonneg)) d.growthBound.coe_nonneg
      simpa only [B,mul_add,Real.exp_add,mul_assoc] using hh

theorem contDiff_vectorGaussianHeat_spatial {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) : ContDiff ℝ 2 (vectorGaussianHeat F v) := by
  obtain ⟨h₁,h₂,h₃⟩ := d.spatial_integral_inputs v
  exact contDiff_integral_of_dominated_derivatives 2 (fieldGaussian n) _ h₁ h₂ h₃

theorem integrable_iteratedFDeriv_vectorGaussianHeat_input {F : Field n → ℝ}
    (d : VectorHeatDatum F) (v : ℝ) (j : ℕ) (hj : j ≤ 2) (x : Field n) :
    Integrable (fun z=>iteratedFDeriv ℝ j F (fieldShift v x z)) (fieldGaussian n) := by
  obtain ⟨_,hm,hb⟩ := d.spatial_integral_inputs v
  obtain ⟨s,hs,B,hBi,hB⟩ := hb x
  have hi := (hBi j hj).mono' (hm j hj x)
    (Eventually.of_forall fun z=>hB j hj x (mem_of_mem_nhds hs) z)
  simpa only [fieldShift,iteratedFDeriv_comp_add_right] using hi

theorem iteratedFDeriv_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) (v : ℝ) (j : ℕ) (hj : j ≤ 2) (x : Field n) :
    iteratedFDeriv ℝ j (vectorGaussianHeat F v) x=
      ∫ z,iteratedFDeriv ℝ j F (fieldShift v x z) ∂fieldGaussian n := by
  obtain ⟨h₁,h₂,h₃⟩ := d.spatial_integral_inputs v
  have hh := iteratedFDeriv_integral_of_dominated_derivatives 2 (fieldGaussian n) _ h₁ h₂ h₃ j hj x
  rw [show vectorGaussianHeat F v=(fun y=>∫ z,F (fieldShift v y z) ∂fieldGaussian n) from rfl]
  simpa only [vectorGaussianHeat,fieldShift,iteratedFDeriv_comp_add_right] using hh

theorem vectorHessian_eq_bilinearOfTwo (F : Field n → ℝ) (x : Field n) :
    vectorHessian F x=vectorBilinearOfTwoCLM n (iteratedFDeriv ℝ 2 F x) := by
  ext u v
  rw [vectorBilinearOfTwo_apply,iteratedFDeriv_two_apply]
  rfl

theorem vectorHessian_vectorGaussianHeat {F : Field n → ℝ}
    (d : VectorHeatDatum F) (v : ℝ) (x : Field n) :
    vectorHessian (vectorGaussianHeat F v) x=
      ∫ z,vectorHessian F (fieldShift v x z) ∂fieldGaussian n := by
  rw [vectorHessian_eq_bilinearOfTwo,iteratedFDeriv_vectorGaussianHeat d v 2 le_rfl x,
    ← (vectorBilinearOfTwoCLM n).integral_comp_comm
      (integrable_iteratedFDeriv_vectorGaussianHeat_input d v 2 le_rfl x)]
  simp only [← vectorHessian_eq_bilinearOfTwo]

theorem integrable_vectorHessian_heat_input {F : Field n → ℝ}
    (d : VectorHeatDatum F) (v : ℝ) (x : Field n) :
    Integrable (fun z=>vectorHessian F (fieldShift v x z)) (fieldGaussian n) := by
  have hi := (vectorBilinearOfTwoCLM n).integrable_comp
    (integrable_iteratedFDeriv_vectorGaussianHeat_input d v 2 le_rfl x)
  simpa only [← vectorHessian_eq_bilinearOfTwo] using hi

end QuantitativePaper
