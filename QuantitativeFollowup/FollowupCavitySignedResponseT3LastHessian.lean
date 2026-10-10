module
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureHessianIntegral

@[expose] public section

/-! The original last Hessian integral in T3, split into its strict-past
and reveal-inclusive future pieces under the actual free measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

def cavitySignedResponseT3LastHessian (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (a β0 : ℝ) (p : Paper.Overlap) : ℝ :=
  2*(∫r,cavitySignedScalarKernelTriple β0 μ (p,r) p*
    cavitySignedResponseMixedHessianMoment D μ a r p ∂parisiFreeMeasure μ a)

private theorem past_kernel_norm_le_one (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ‖cavitySignedScalarPastTripleKernel β0 μ r p‖≤1 := by
  by_cases h : r<p
  · have hs := cavitySignedScalarKernelTriple_square_le β0 μ p r p
    have hprod : Gamma β0 μ (min p r)*Gamma β0 μ p≤1 :=
      (mul_le_mul (scalarGamma_le_one β0 μ (min p r) (min p r).property)
        (scalarGamma_le_one β0 μ p p.property) (scalarGamma_nonneg β0 μ p) zero_le_one).trans_eq (one_mul (1:ℝ))
    have hs' := hs.trans hprod
    rw [cavitySignedScalarPastTripleKernel,if_pos h,Real.norm_eq_abs]
    nlinarith [sq_abs (cavitySignedScalarKernelTriple β0 μ (p,r) p),
      abs_nonneg (cavitySignedScalarKernelTriple β0 μ (p,r) p)]
  · simp only [cavitySignedScalarPastTripleKernel,if_neg h,norm_zero,zero_le_one]

theorem cavitySignedResponse_T3_last_Hessian_integral_split (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) :
    (∫p,cavitySignedResponseT3LastHessian D μ a β0 p ∂parisiFreeMeasure μ a)=
      2*(∫r,∫p,cavitySignedScalarPastTripleKernel β0 μ r p*
        cavitySignedResponseMixedHessianMoment D μ a r p ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)+
      2*(∫r,∫p,cavitySignedScalarFutureTripleKernel β0 μ r p*
        cavitySignedResponseMixedHessianMoment D μ a r p ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a) := by
  let ν := parisiFreeMeasure μ a
  let B := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  let F := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedScalarPastTripleKernel β0 μ z.1 z.2*B z
  let G := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedScalarFutureTripleKernel β0 μ z.1 z.2*B z
  have hB := measurable_cavitySignedResponseMixedHessianMoment D μ a
  have hF : Integrable F (ν.prod ν) := by
    apply (integrable_const 1).mono'
      ((measurable_cavitySignedScalarPastTripleKernel β0 hβ0 μ).mul hB).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖cavitySignedScalarPastTripleKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤1
      rw [norm_mul]
      exact (mul_le_mul (past_kernel_norm_le_one β0 μ z.1 z.2)
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a z.1 z.2)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have hG : Integrable G (ν.prod ν) := by
    apply (integrable_const 1).mono'
      ((measurable_cavitySignedScalarFutureTripleKernel β0 hβ0 μ).mul hB).aestronglyMeasurable
    exact .of_forall fun z=>by
      change ‖cavitySignedScalarFutureTripleKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤1
      rw [norm_mul]
      exact (mul_le_mul ((cavitySignedScalarFutureTripleKernel_norm_le β0 μ z.1 z.2).trans
        (scalarGamma_le_one β0 μ z.2 z.2.property))
        (norm_cavitySignedResponseMixedHessianMoment_le D μ a z.1 z.2)
        (norm_nonneg _) zero_le_one).trans_eq (by norm_num)
  have he (r p : Paper.Overlap) :
      cavitySignedScalarKernelTriple β0 μ (p,r) p*cavitySignedResponseMixedHessianMoment D μ a r p=
        F (r,p)+G (r,p) := by
    by_cases h : r<p
    · have hh : ¬p≤r := not_le.mpr h
      simp [F,G,B,cavitySignedScalarPastTripleKernel,cavitySignedScalarFutureTripleKernel,h,hh]
    · have hh : p≤r := le_of_not_gt h
      simp [F,G,B,cavitySignedScalarPastTripleKernel,cavitySignedScalarFutureTripleKernel,h,hh]
  simp only [cavitySignedResponseT3LastHessian]
  rw [integral_const_mul]
  simp_rw [he]
  rw [←integral_integral_swap (hF.add hG)]
  change 2*(∫r,∫p,(F+G) (r,p) ∂ν ∂ν)=_
  rw [←integral_prod _ (hF.add hG)]
  change 2*(∫z,F z+G z ∂ν.prod ν)=_
  rw [integral_add hF hG,integral_prod _ hF,integral_prod _ hG,mul_add]

theorem cavitySignedResponse_T3_last_Hessian_original_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    |∫p,cavitySignedResponseT3LastHessian D μ a β0 p ∂parisiFreeMeasure μ a|≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  rw [cavitySignedResponse_T3_last_Hessian_integral_split D μ a β0 hβ0]
  exact (abs_add_le _ _).trans ((add_le_add
    (cavitySignedResponse_T3_past_Hessian_integral_bound D μ a β0 hβ0 ha)
    (cavitySignedResponse_T3_future_Hessian_integral_bound D μ a β0 hβ0 ha)).trans_eq (by ring))

end QuantitativeFollowup
