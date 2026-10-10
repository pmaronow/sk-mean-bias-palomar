module
public import QuantitativeFollowup.FollowupCavitySignedResponseMixedHessian
public import QuantitativeFollowup.FollowupCavitySignedResponseFutureScalarKernel
public import QuantitativeFollowup.FollowupCavitySignedResponseIntegratedPairing

@[expose] public section

/-! Actual integrated future-Hessian and score contributions in T3.
All scalar kernels, moments, joint measurability and finite-measure
integrability are discharged internally. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128

theorem measurable_joint_cavitySignedResponseMixedHessian (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n =>
      cavitySignedResponseMixedHessian D μ z.1.1 z.1.2 z.2) := by
  have hrmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n => (z.1.1,z.2)) :=
    measurable_fst.fst.prodMk measurable_snd
  have hlmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n => (z.1.2,z.2)) :=
    measurable_fst.snd.prodMk measurable_snd
  have hTmap : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n =>
      (z.1.2,anisotropicProcessParameter D μ z.1.2 z.2)) :=
    measurable_fst.snd.prodMk ((measurable_uncurry_anisotropicProcessParameter D μ).comp hlmap)
  have hT := (continuous_anisotropicMeasureTailSecondDifferential_joint D μ).measurable.comp hTmap
  have hr := (anisotropicFieldInjection n).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hrmap)
  have hl := (anisotropicFieldInjection n).continuous.measurable.comp
    ((measurable_uncurry_anisotropicProcessMagnetization D μ).comp hlmap)
  have hev : Continuous (fun z : ((AnisotropicParameter n→L[ℝ](AnisotropicParameter n→L[ℝ]ℝ))×
      AnisotropicParameter n)×AnisotropicParameter n =>z.1.1 z.1.2 z.2) :=
    (continuous_fst.fst.clm_apply continuous_fst.snd).clm_apply continuous_snd
  have h := hev.measurable.comp ((hT.prodMk hr).prodMk hl)
  dsimp only [Function.comp_def] at h
  exact h

theorem measurable_cavitySignedResponseMixedHessianMoment (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Measurable (Function.uncurry (cavitySignedResponseMixedHessianMoment D μ a)) :=
  ((measurable_joint_cavitySignedResponseMixedHessian D μ).stronglyMeasurable.integral_prod_right'
    (ν := anisotropicMeasureSampleLaw D μ a)).measurable.div_const _

theorem norm_cavitySignedResponseMixedHessianMoment_le (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (r l : Paper.Overlap) :
    ‖cavitySignedResponseMixedHessianMoment D μ a r l‖≤1 := by
  have h := norm_integral_le_of_norm_le (integrable_const (μ := anisotropicMeasureSampleLaw D μ a) ((n:ℝ)^2))
    (.of_forall (norm_cavitySignedResponseMixedHessian_le D μ r l))
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at h
  unfold cavitySignedResponseMixedHessianMoment
  rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
  by_cases hn : n=0
  · simp [hn]
  · have hn0 : 0<(n:ℝ)^2 := sq_pos_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
    exact (div_le_iff₀ hn0).2 (by simpa only [one_mul] using h)

theorem cavitySignedResponse_T3_future_explicit_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0) (ha : a∈Icc (0:ℝ) 1) :
    |(2:ℝ)*(∫r,∫l,cavitySignedScalarStrictFutureKernel β0 μ r l*
      cavitySignedResponseMixedHessianMoment D μ a r l ∂parisiFreeMeasure μ a ∂parisiFreeMeasure μ a)|≤
      2*cavitySignedResponseWeightedJ D μ a β0 Finset.univ := by
  let ν := parisiFreeMeasure μ a
  let χ := cavitySignedResponseSqrtMoment D μ a β0 Finset.univ
  let f := fun z : Paper.Overlap×Paper.Overlap => cavitySignedScalarStrictFutureKernel β0 μ z.1 z.2*
    cavitySignedResponseMixedHessianMoment D μ a z.1 z.2
  let g := fun z : Paper.Overlap×Paper.Overlap => χ z.1*χ z.2
  have hf : Measurable f := (measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ).mul
    (measurable_cavitySignedResponseMixedHessianMoment D μ a)
  have hχm := measurable_cavitySignedResponseSqrtMoment D μ a β0 hβ0 Finset.univ
  have hχB := norm_cavitySignedResponseSqrtMoment_le D μ a β0 Finset.univ
  have hχI : Integrable χ ν := (integrable_const _).mono' hχm.aestronglyMeasurable (.of_forall hχB)
  have hg : Integrable g (ν.prod ν) := (integrable_const _).mono'
    ((hχm.comp measurable_fst).mul (hχm.comp measurable_snd)).aestronglyMeasurable
    (.of_forall fun z=>(norm_mul _ _).trans_le (mul_le_mul (hχB z.1) (hχB z.2) (norm_nonneg _) (Real.sqrt_nonneg _)))
  have hpoint (z : Paper.Overlap×Paper.Overlap) : ‖f z‖≤g z := by
    by_cases hrl : z.1<z.2
    · have hK := cavitySignedScalarFutureCovarianceKernel_square_le β0 μ z.1 z.2
      have hM := cavitySignedResponseMixedHessianMoment_square_le D μ a z.1 z.2 hrl.le
      have hprod := mul_le_mul hK hM (sq_nonneg _) (mul_nonneg (scalarGamma_nonneg β0 μ z.1) (scalarGamma_nonneg β0 μ z.2))
      have hr := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ z.1)
        (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ z.1))
      have hl := Real.sq_sqrt (mul_nonneg (scalarGamma_nonneg β0 μ z.2)
        (cavitySignedResponseCovarianceMoment_nonneg D μ a Finset.univ z.2))
      change ‖cavitySignedScalarStrictFutureKernel β0 μ z.1 z.2*
        cavitySignedResponseMixedHessianMoment D μ a z.1 z.2‖≤χ z.1*χ z.2
      rw [cavitySignedScalarStrictFutureKernel,if_pos hrl,Real.norm_eq_abs]
      have hs : (cavitySignedScalarFutureCovarianceKernel β0 μ z.1 z.2*
          cavitySignedResponseMixedHessianMoment D μ a z.1 z.2)^2≤(χ z.1*χ z.2)^2 := by
        unfold χ cavitySignedResponseSqrtMoment
        simp only [mul_pow,hr,hl]
        simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hprod
      have hh : |cavitySignedScalarFutureCovarianceKernel β0 μ z.1 z.2*
          cavitySignedResponseMixedHessianMoment D μ a z.1 z.2|≤Real.sqrt ((χ z.1*χ z.2)^2) :=
        Real.le_sqrt_of_sq_le (by simpa only [sq_abs] using hs)
      have hχprod : 0≤χ z.1*χ z.2 := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rwa [Real.sqrt_sq hχprod] at hh
    · simp only [f,g,cavitySignedScalarStrictFutureKernel,if_neg hrl,zero_mul,norm_zero]
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

theorem cavitySignedResponse_T3_future_score_integral_bound (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a β0 : ℝ) (hβ0 : β0≠0)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) (hn : 0<n) :
    |∫r,∫p,cavitySignedResponseScore D μ a r p*
      anisotropicWeightedSelfOverlap D μ a (cavitySignedScalarStrictFutureKernel β0 μ r) Finset.univ p.1
      ∂anisotropicMeasureSpinPathLaw D μ a ∂parisiFreeMeasure μ a|≤
      4*cavitySignedResponseWeightedJ D μ a β0 Finset.univ :=
  cavitySignedResponse_integrated_score_pairing D μ a β0 hβ0 ha hμ hn
    (cavitySignedScalarStrictFutureKernel β0 μ) (measurable_cavitySignedScalarStrictFutureKernel β0 hβ0 μ)
    (cavitySignedScalarStrictFutureKernel_square_le β0 μ)

end QuantitativeFollowup
