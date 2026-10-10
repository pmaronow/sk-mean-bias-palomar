module
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessianIntegrals
public import QuantitativeFollowup.FollowupCavitySignedResponseScalarDoubleKernels

@[expose] public section

/-! Literal strict-past Hessian contribution in the last integral of T3. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

def cavitySignedScalarPastTripleKernel (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ :=
  if r<p then cavitySignedScalarKernelTriple β0 μ (p,r) p else 0

theorem measurable_cavitySignedScalarPastTripleKernel (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (cavitySignedScalarPastTripleKernel β0 μ)) := by
  classical
  have hmap : Continuous (fun z : Paper.Overlap×Paper.Overlap=>((z.2,z.1),z.2)) :=
    (continuous_snd.prodMk continuous_fst).prodMk continuous_snd
  unfold Function.uncurry cavitySignedScalarPastTripleKernel
  exact ((continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).comp hmap).measurable.ite
    (measurableSet_lt measurable_fst measurable_snd) measurable_const

theorem cavitySignedResponse_T3_past_Hessian_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    |(2:ℝ)*(∫r,∫l,cavitySignedScalarPastTripleKernel β0 μ r l*
      cavitySignedResponseMixedHessianMoment D μ a r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let χ := cavitySignedResponseSqrtMoment D μ a β0 Finset.univ
  let f := fun z : Paper.Overlap×Paper.Overlap => cavitySignedScalarPastTripleKernel β0 μ z.1 z.2*
    cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  let g := fun z : Paper.Overlap×Paper.Overlap => χ z.1*χ z.2
  have hf : Measurable f := (measurable_cavitySignedScalarPastTripleKernel β0 hβ0 μ).mul
    (measurable_cavitySignedResponseMixedHessianMoment D μ a)
  have hχm := measurable_cavitySignedResponseSqrtMoment D μ a β0 hβ0 Finset.univ
  have hχB := norm_cavitySignedResponseSqrtMoment_le D μ a β0 Finset.univ
  have hχI : Integrable χ ν := (integrable_const _).mono' hχm.aestronglyMeasurable (.of_forall hχB)
  have hg : Integrable g (ν.prod ν) := (integrable_const _).mono'
    ((hχm.comp measurable_fst).mul (hχm.comp measurable_snd)).aestronglyMeasurable
    (.of_forall fun z=>(norm_mul _ _).trans_le (mul_le_mul (hχB z.1) (hχB z.2) (norm_nonneg _) (Real.sqrt_nonneg _)))
  have hpoint (z : Paper.Overlap×Paper.Overlap) : ‖f z‖≤g z := by
    by_cases hrl : z.1<z.2
    · have hK := cavitySignedScalarKernelTriple_square_le β0 μ z.2 z.1 z.2
      rw [min_eq_right (show (z.1:ℝ)≤(z.2:ℝ) from hrl.le)] at hK
      have hM := cavitySignedResponseMixedHessianMoment_square_le D μ a z.1 z.2 hrl.le
      have hprod := mul_le_mul hK hM (sq_nonneg _) (mul_nonneg (scalarGamma_nonneg β0 μ z.1) (scalarGamma_nonneg β0 μ z.2))
      have hr := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ z.1)
        (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ z.1))
      have hl := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ z.2)
        (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ z.2))
      change ‖cavitySignedScalarPastTripleKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤χ z.1*χ z.2
      rw [cavitySignedScalarPastTripleKernel,if_pos hrl,Real.norm_eq_abs]
      have hs : (cavitySignedScalarKernelTriple β0 μ (z.2,z.1) z.2*
          cavitySignedResponseMixedHessianMoment D μ a z.1 z.2)^2≤(χ z.1*χ z.2)^2 := by
        unfold χ cavitySignedResponseSqrtMoment
        simp only [mul_pow,hr,hl]
        simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hprod
      have hh : |cavitySignedScalarKernelTriple β0 μ (z.2,z.1) z.2*
          cavitySignedResponseMixedHessianMoment D μ a z.1 z.2|≤Real.sqrt ((χ z.1*χ z.2)^2) :=
        Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hs)
      have hχprod : 0≤χ z.1*χ z.2 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rwa [Real.sqrt_sq hχprod] at hh
    · simp only [f,g,cavitySignedScalarPastTripleKernel,if_neg hrl,zero_mul,norm_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h := norm_integral_le_of_norm_le hg (.of_forall hpoint)
  rw [integral_prod_mul] at h
  have hs := cavitySignedResponse_sqrt_free_integral_le D μ a β0 ha hβ0 Finset.univ
  have hχ0 : 0≤(∫q,χ q ∂ν) := integral_nonneg fun q=>Real.sqrt_nonneg _
  have hb := h.trans ((mul_self_le_mul_self hχ0 hs).trans_eq
    (by simpa only [pow_two] using Real.sq_sqrt (cavitySignedResponseWeightedJ_nonneg D μ a β0 Finset.univ)))
  have hfi : Integrable f (ν.prod ν) := hg.mono' hf.aestronglyMeasurable (.of_forall hpoint)
  rw [integral_prod _ hfi,Real.norm_eq_abs] at hb
  rw [abs_mul]
  norm_num
  exact hb

end QuantitativeFollowup
