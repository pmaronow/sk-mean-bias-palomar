module
public import QuantitativeFollowup.GaussianLinearResponse

@[expose] public section

/-! Actual differentiation of a Gaussian observable along a changing linear
covariance input. The derivative is obtained by dominated differentiation
and Gaussian integration by parts, then normalized by the genuine partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

 def gaussianLinearMean (F : Field m → ℝ) (A : Field n →L[ℝ] Field m) (x : Field m) : ℝ :=
  ∫ z,F (x+A z) ∂fieldGaussian n

 theorem integrable_gaussianLinear_input {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A : Field n →L[ℝ] Field m) (x : Field m) :
    Integrable (fun z => F (x+A z)) (fieldGaussian n) := by
  apply ((SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*‖A‖)).const_mul
    (d.growthBound*Real.exp (d.rate*‖x‖))).mono'
      ((d.regularity.continuous.comp (continuous_const.add A.continuous)).aestronglyMeasurable)
  exact .of_forall fun z => by
    change ‖F (x+A z)‖ ≤ d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*‖A‖)*‖z‖)
    apply (d.value_bound _).trans
    have hn : ‖x+A z‖ ≤ ‖x‖+‖A‖*‖z‖ :=
      (norm_add_le _ _).trans (add_le_add le_rfl (A.le_opNorm z))
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    simpa only [mul_add,Real.exp_add,mul_assoc] using hh

 theorem gaussianLinear_curve_derivative_bound {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : Field n →L[ℝ] Field m) (x : Field m) (K L : ℝ) (hK : 0 ≤ K)
    (hA : ‖A‖ ≤ K) (hB : ‖B‖ ≤ L) (z : Field n) :
    ‖fderiv ℝ F (x+A z) (B z)‖ ≤ L*d.growthBound*Real.exp (d.rate*‖x‖)*
      Real.exp ((d.rate*K+1)*‖z‖) := by
  have hL : 0 ≤ L := (norm_nonneg B).trans hB
  have hn : ‖x+A z‖ ≤ ‖x‖+K*‖z‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl ((A.le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hA (norm_nonneg _))))
  have hd : ‖fderiv ℝ F (x+A z)‖ ≤ d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*K)*‖z‖) := by
    apply (d.first_bound _).trans
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hn d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    simpa only [mul_add,Real.exp_add,mul_assoc] using hh
  have hz : ‖z‖ ≤ Real.exp ‖z‖ := (by linarith : ‖z‖ ≤ ‖z‖+1).trans (Real.add_one_le_exp _)
  have hb : ‖B z‖ ≤ L*Real.exp ‖z‖ := (B.le_opNorm z).trans
    (mul_le_mul hB hz (norm_nonneg _) hL)
  calc
    _ ≤ ‖fderiv ℝ F (x+A z)‖*‖B z‖ := (fderiv ℝ F _).le_opNorm _
    _ ≤ (d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*K)*‖z‖))*(L*Real.exp ‖z‖) :=
      mul_le_mul hd hb (norm_nonneg _) (by positivity)
    _ = _ := by rw [add_mul,one_mul,Real.exp_add];ring

 theorem hasDerivAt_gaussianLinearMean {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hAB : ∀ u∈S,HasDerivAt A (B u) u) (K L : ℝ) (hK : 0 ≤ K)
    (hA : ∀ u∈S,‖A u‖ ≤ K) (hB : ∀ u∈S,‖B u‖ ≤ L) (x : Field m) :
    HasDerivAt (fun u => gaussianLinearMean F (A u) x)
      (∫ z,∑ i : Fin n,vectorHessian F (x+A a z)
        (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) ∂fieldGaussian n) a := by
  let bound : Field n → ℝ := fun z => L*d.growthBound*Real.exp (d.rate*‖x‖)*
    Real.exp ((d.rate*K+1)*‖z‖)
  have hi : Integrable bound (fieldGaussian n) :=
    (SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*K+1)).const_mul _
  have hdc : Continuous (fderiv ℝ F) := (d.regularity.fderiv_right (m := 1) (by norm_num)).continuous
  have hdm : AEStronglyMeasurable (fun z => fderiv ℝ F (x+A a z) (B a z)) (fieldGaussian n) :=
    ((hdc.comp (continuous_const.add (A a).continuous)).clm_apply (B a).continuous).aestronglyMeasurable
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun u z => F (x+A u z)) (F' := fun u z => fderiv ℝ F (x+A u z) (B u z))
    (bound := bound) (s := S) hS
    (.of_forall fun u => (d.regularity.continuous.comp (continuous_const.add (A u).continuous)).aestronglyMeasurable)
    (integrable_gaussianLinear_input d (A a) x) hdm
    (.of_forall fun z u hu => gaussianLinear_curve_derivative_bound d (A u) (B u) x K L hK (hA u hu) (hB u hu) z)
    hi (.of_forall fun z u hu => by
      have hs : HasDerivAt (fun v => x+A v z) (B u z) u := by
        simpa only [zero_add,map_zero,add_zero] using ((hAB u hu).clm_apply (hasDerivAt_const u z)).const_add x
      exact (d.regularity.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt u hs)).2
  exact hd.congr_deriv (integral_gaussianLinear_covariance_response d (A a) (B a) x).2

 def gaussianLinearNormalizedMean (F H : Field m → ℝ) (A : Field n →L[ℝ] Field m) (x : Field m) : ℝ :=
  gaussianLinearMean F A x/gaussianLinearMean H A x

 theorem hasDerivAt_gaussianLinearNormalizedMean {F H : Field m → ℝ}
    (dF : VectorHeatDatum F) (dH : VectorHeatDatum H)
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hAB : ∀ u∈S,HasDerivAt A (B u) u) (K L : ℝ) (hK : 0 ≤ K)
    (hA : ∀ u∈S,‖A u‖ ≤ K) (hB : ∀ u∈S,‖B u‖ ≤ L) (x : Field m)
    (hH : gaussianLinearMean H (A a) x ≠ 0) :
    HasDerivAt (fun u => gaussianLinearNormalizedMean F H (A u) x)
      (((∫ z,∑ i : Fin n,vectorHessian F (x+A a z)
        (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) ∂fieldGaussian n)*gaussianLinearMean H (A a) x-
        gaussianLinearMean F (A a) x*(∫ z,∑ i : Fin n,vectorHessian H (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) ∂fieldGaussian n))/
        gaussianLinearMean H (A a) x^2) a :=
  (hasDerivAt_gaussianLinearMean dF A B a S hS hAB K L hK hA hB x).div
    (hasDerivAt_gaussianLinearMean dH A B a S hS hAB K L hK hA hB x) hH

end QuantitativeFollowup
