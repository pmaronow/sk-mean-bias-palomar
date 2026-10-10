module
public import QuantitativePaper.VectorExponentialHeatData

@[expose] public section

/-! Genuine variance differentiation of vector Gaussian heat integrals.
Local domination is derived from exponential growth of the actual first
spatial derivative and the positive variance interval. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorGaussianHeat (F : Field n → ℝ) (v : ℝ) (x : Field n) : ℝ :=
  ∫ z,F (fieldShift v x z) ∂fieldGaussian n

theorem VectorHeatDatum.variance_derivative_bound {F : Field n → ℝ}
    (d : VectorHeatDatum F) (x : Field n) (a b u : ℝ) (ha : 0 < a)
    (hau : a ≤ u) (hub : u ≤ b) (z : Field n) :
    ‖fderiv ℝ F (fieldShift u x z) ((1/(2*Real.sqrt u)) • z)‖ ≤
      (d.growthBound*Real.exp (d.rate*‖x‖)/Real.sqrt a)*
        Real.exp ((d.rate*Real.sqrt b+1)*‖z‖) := by
  have hu : 0 < u := ha.trans_le hau
  have hra : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hru : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu
  have hden : Real.sqrt a ≤ 2*Real.sqrt u := by
    have hh := Real.sqrt_le_sqrt hau
    linarith
  have hi : 1/(2*Real.sqrt u) ≤ 1/Real.sqrt a := one_div_le_one_div_of_le hra hden
  have hn : ‖fieldShift u x z‖ ≤ ‖x‖+Real.sqrt b*‖z‖ := by
    have hh := norm_add_le x (Real.sqrt u • z)
    simp only [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hh
    exact hh.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hub) (norm_nonneg _)))
  have hd : ‖fderiv ℝ F (fieldShift u x z)‖ ≤
      d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*Real.sqrt b)*‖z‖) := by
    apply (d.first_bound _).trans
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    simpa only [mul_add,Real.exp_add,mul_assoc] using hh
  have hz : ‖z‖ ≤ Real.exp ‖z‖ := (by linarith : ‖z‖ ≤ ‖z‖+1).trans (Real.add_one_le_exp _)
  calc
    _ ≤ ‖fderiv ℝ F (fieldShift u x z)‖*‖(1/(2*Real.sqrt u)) • z‖ := (fderiv ℝ F _).le_opNorm _
    _ ≤ (d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*Real.sqrt b)*‖z‖))*
        ((1/Real.sqrt a)*Real.exp ‖z‖) := by
      rw [norm_smul,Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul hd (mul_le_mul hi hz (norm_nonneg _) (by positivity))
        (by positivity) (by positivity)
    _ = _ := by rw [add_mul,one_mul,Real.exp_add];ring

theorem hasDerivAt_vectorGaussianHeat_scale {F : Field n → ℝ}
    (d : VectorHeatDatum F) {v : ℝ} (hv : 0 < v) (x : Field n) :
    HasDerivAt (fun u=>vectorGaussianHeat F u x)
      (∫ z,fderiv ℝ F (fieldShift v x z) ((1/(2*Real.sqrt v)) • z) ∂fieldGaussian n) v := by
  let S := Ioo (v/2) (v+1)
  have hS : S∈𝓝 v := isOpen_Ioo.mem_nhds ⟨by linarith,by linarith⟩
  have ha : 0 < v/2 := by linarith
  let B : Field n → ℝ := fun z=>(d.growthBound*Real.exp (d.rate*‖x‖)/Real.sqrt (v/2))*
    Real.exp ((d.rate*Real.sqrt (v+1)+1)*‖z‖)
  have hBi : Integrable B (fieldGaussian n) :=
    (SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*Real.sqrt (v+1)+1)).const_mul _
  have hDc : Continuous (fderiv ℝ F) :=
    (d.regularity.fderiv_right (m := 1) (by norm_num)).continuous
  have hDm : AEStronglyMeasurable
      (fun z=>fderiv ℝ F (fieldShift v x z) ((1/(2*Real.sqrt v)) • z)) (fieldGaussian n) := by
    apply Continuous.aestronglyMeasurable
    exact (hDc.comp (by unfold fieldShift;fun_prop)).clm_apply
      (continuous_id.const_smul (1/(2*Real.sqrt v)))
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z=>F (fieldShift u x z))
    (F' := fun u z=>fderiv ℝ F (fieldShift u x z) ((1/(2*Real.sqrt u)) • z))
    (bound := B) (s := S) hS
    (Eventually.of_forall fun u=>(d.regularity.continuous.comp (by unfold fieldShift;fun_prop)).aestronglyMeasurable)
    (d.integrable_shift v x) hDm
    (Eventually.of_forall fun z u hu=>d.variance_derivative_bound x (v/2) (v+1) u ha hu.1.le hu.2.le z)
    hBi ?_).2
  apply Eventually.of_forall
  intro z u hu
  have hup : 0 < u := ha.trans hu.1
  have hshift : HasDerivAt (fun w=>fieldShift w x z) ((1/(2*Real.sqrt u)) • z) u := by
    simpa only [fieldShift,zero_add] using
      (hasDerivAt_const u x).fun_add ((Real.hasDerivAt_sqrt hup.ne').smul_const z)
  exact (d.regularity.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt u hshift

end QuantitativePaper
