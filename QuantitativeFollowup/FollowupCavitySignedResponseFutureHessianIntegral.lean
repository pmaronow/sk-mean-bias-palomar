module
public import QuantitativeFollowup.FollowupCavitySignedResponseHessianPastPairing
public import QuantitativeFollowup.FollowupCavitySignedResponsePastHessianIntegral

@[expose] public section

/-! Literal future part of the final Hessian integral in T3, including
the reveal diagonal.  Its martingale reduction is proved under the
actual marked law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128

theorem cavitySignedResponseMixedHessianMoment_diagonal_bounds (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    0≤cavitySignedResponseMixedHessianMoment D μ a p p ∧
      cavitySignedResponseMixedHessianMoment D μ a p p≤
        cavitySignedResponseCovarianceMoment D μ a Finset.univ p := by
  have hb : 0≤cavitySignedResponseMixedHessianMoment D μ a p p :=
    div_nonneg (integral_nonneg fun sample=>cavitySignedResponseFieldHessian_nonneg D μ p _ _)
      (sq_nonneg _)
  have hs := cavitySignedResponseMixedHessianMoment_square_le D μ a p p le_rfl
  have hj := cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ p
  exact ⟨hb,by nlinarith⟩

def cavitySignedScalarFutureTripleKernel (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) : ℝ :=
  if p≤r then cavitySignedScalarKernelTriple β0 μ (p,r) p else 0

theorem measurable_cavitySignedScalarFutureTripleKernel (β0 : ℝ) (hβ0 : β0≠0)
    (μ : Paper.ParisiMeasure) :
    Measurable (Function.uncurry (cavitySignedScalarFutureTripleKernel β0 μ)) := by
  classical
  have hmap : Continuous (fun z : Paper.Overlap×Paper.Overlap=>((z.2,z.1),z.2)) :=
    (continuous_snd.prodMk continuous_fst).prodMk continuous_snd
  unfold Function.uncurry cavitySignedScalarFutureTripleKernel
  exact ((continuous_cavitySignedScalarKernelTriple β0 hβ0 μ).comp hmap).measurable.ite
    (measurableSet_le measurable_snd measurable_fst) measurable_const

theorem cavitySignedScalarFutureTripleKernel_norm_le (β0 : ℝ) (μ : Paper.ParisiMeasure)
    (r p : Paper.Overlap) :
    ‖cavitySignedScalarFutureTripleKernel β0 μ r p‖≤Gamma β0 μ p := by
  by_cases h : p≤r
  · have hs := cavitySignedScalarKernelTriple_square_le β0 μ p r p
    rw [min_eq_left (show (p:ℝ)≤(r:ℝ) from h)] at hs
    rw [cavitySignedScalarFutureTripleKernel,if_pos h,Real.norm_eq_abs]
    nlinarith [sq_abs (cavitySignedScalarKernelTriple β0 μ (p,r) p),
      abs_nonneg (cavitySignedScalarKernelTriple β0 μ (p,r) p),scalarGamma_nonneg β0 μ p]
  · simpa only [cavitySignedScalarFutureTripleKernel,if_neg h,Real.norm_eq_abs,abs_zero] using scalarGamma_nonneg β0 μ p

theorem cavitySignedResponse_T3_future_Hessian_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    |(2:ℝ)*(∫r,∫p,cavitySignedScalarFutureTripleKernel β0 μ r p*
      cavitySignedResponseMixedHessianMoment D μ a r p ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let f := fun z : Paper.Overlap×Paper.Overlap=>cavitySignedScalarFutureTripleKernel β0 μ z.1 z.2*
    cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  let g := fun z : Paper.Overlap×Paper.Overlap=>Gamma β0 μ z.2*cavitySignedResponseCovarianceMoment D μ a Finset.univ z.2
  let B := anisotropicProcessCovarianceEnergyBound (Finset.univ : Finset (Fin n))/(n:ℝ)^2
  have hΓ : Measurable (fun p : Paper.Overlap=>Gamma β0 μ p) :=
    ((continuousOn_Gamma β0 hβ0 μ).comp_continuous continuous_subtype_val (fun p=>p.property)).measurable
  have hj := measurable_cavitySignedResponseCovarianceMoment D μ a Finset.univ
  have hgj : Measurable (fun p : Paper.Overlap=>Gamma β0 μ p*cavitySignedResponseCovarianceMoment D μ a Finset.univ p) := hΓ.mul hj
  have hgB (z : Paper.Overlap×Paper.Overlap) : ‖g z‖≤B := by
    rw [norm_mul,Real.norm_of_nonneg (scalarGamma_nonneg β0 μ z.2)]
    have hb := norm_cavitySignedResponseCovarianceMoment_le D μ a Finset.univ z.2
    simp only [Finset.card_univ,Fintype.card_fin] at hb
    exact (mul_le_mul (scalarGamma_le_one β0 μ z.2 z.2.property) hb (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hg : Integrable g (ν.prod ν) := (integrable_const B).mono'
    (hgj.comp measurable_snd).aestronglyMeasurable (.of_forall hgB)
  have hf : Measurable f := (measurable_cavitySignedScalarFutureTripleKernel β0 hβ0 μ).mul
    (measurable_cavitySignedResponseMixedHessianMoment D μ a)
  have hpoint (z : Paper.Overlap×Paper.Overlap) : ‖f z‖≤g z := by
    by_cases hpr : z.2≤z.1
    · have hb := cavitySignedResponseMixedHessianMoment_diagonal_bounds D μ a z.2
      have he := cavitySignedResponseMixedHessianMoment_future_eq D μ a z.2 z.1 hpr
      change ‖cavitySignedScalarFutureTripleKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤_
      rw [norm_mul,he,Real.norm_of_nonneg hb.1]
      exact mul_le_mul (cavitySignedScalarFutureTripleKernel_norm_le β0 μ z.1 z.2)
        hb.2 hb.1 (scalarGamma_nonneg β0 μ z.2)
    · simp only [f,cavitySignedScalarFutureTripleKernel,if_neg hpr,zero_mul,norm_zero]
      exact mul_nonneg (scalarGamma_nonneg β0 μ z.2) (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ z.2)
  have hb := norm_integral_le_of_norm_le hg (.of_forall hpoint)
  have he : (∫z,g z ∂ν.prod ν)=ν.real Set.univ*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
    rw [integral_prod _ hg]
    change (∫_r,cavitySignedResponseWeightedJ D μ a β0 Finset.univ ∂ν)=_
    simp only [integral_const,smul_eq_mul]
  rw [he] at hb
  have hν1 : ν.real Set.univ≤1 := by
    simp only [ν,Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)]
    linarith [ha.1]
  have hb' := hb.trans (mul_le_of_le_one_left (cavitySignedResponseWeightedJ_nonneg D μ a β0 Finset.univ) hν1)
  have hfi : Integrable f (ν.prod ν) := hg.mono' hf.aestronglyMeasurable (.of_forall hpoint)
  rw [integral_prod _ hfi,Real.norm_eq_abs] at hb'
  rw [abs_mul]
  norm_num
  exact hb'

end QuantitativeFollowup
