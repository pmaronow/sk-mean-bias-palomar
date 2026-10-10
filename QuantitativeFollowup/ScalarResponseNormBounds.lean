module
public import QuantitativeFollowup.ScalarResponseSymmetry
public import FourPapersCommon.L2IntegralBounds

@[expose] public section

/-! Genuine dimension-free-in-profile bounds for the literal scalar
response. The min-level terms are estimated against their original free
measure, preserving atoms and AE representatives in the later extension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

def scalarResponseKernelBound (β : ℝ) : ℝ := 1+2*Real.exp (β^2)

theorem scalarResponseKernelBound_ge_one (β : ℝ) : 1 ≤ scalarResponseKernelBound β := by
  dsimp only [scalarResponseKernelBound]
  linarith [Real.exp_pos (β^2)]

theorem scalarResponseKernel_bounds (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) :
    ‖scalarResponseKernel0 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel1 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel2 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel3 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel4 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel5 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel6 β μ p r ell‖ ≤ scalarResponseKernelBound β ∧
    ‖scalarResponseKernel7 β μ p r ell‖ ≤ scalarResponseKernelBound β := by
  have h0 : ‖scalarResponseKernel0 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel0,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel0_integrand_bound β μ p r ell))
  have h1 : ‖scalarResponseKernel1 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel1,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel1_integrand_bound β μ p r ell))
  have h2 : ‖scalarResponseKernel2 β μ p r ell‖ ≤ 2*Real.exp (β^2) := by
    simpa only [scalarResponseKernel2,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel2_integrand_bound β μ p r ell))
  have h3 : ‖scalarResponseKernel3 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel3,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel3_integrand_bound β μ p r ell))
  have h4 : ‖scalarResponseKernel4 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel4,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel4_integrand_bound β μ p r ell))
  have h5 : ‖scalarResponseKernel5 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel5,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel5_integrand_bound β μ p r ell))
  have h6 : ‖scalarResponseKernel6 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel6,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel6_integrand_bound β μ p r ell))
  have h7 : ‖scalarResponseKernel7 β μ p r ell‖ ≤ 1 := by
    simpa only [scalarResponseKernel7,probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=canonicalBrownianMeasure) (.of_forall (scalarResponseKernel7_integrand_bound β μ p r ell))
  have hR := scalarResponseKernelBound_ge_one β
  exact ⟨h0.trans hR,h1.trans hR,h2.trans (by dsimp only [scalarResponseKernelBound];linarith),
    h3.trans hR,h4.trans hR,h5.trans hR,h6.trans hR,h7.trans hR⟩

theorem scalarFreeMeasure_mass_le_one (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) :
    (parisiFreeMeasure μ a).real univ ≤ 1 := by
  rw [Measure.real,parisiFreeMeasure_univ,ENNReal.toReal_ofReal (by linarith [ha.2])]
  linarith [ha.1]

theorem norm_integral_bounded_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f K : Ω→ℝ) (hf : Integrable (fun q=>|f q|) ν)
    (R : ℝ) (_hR : 0 ≤ R) (hK : ∀q,‖K q‖ ≤ R) :
    ‖∫q,K q*f q ∂ν‖ ≤ R*(∫q,|f q| ∂ν) := by
  have he := norm_integral_le_of_norm_le (f:=fun q=>K q*f q) (hf.const_mul R) (.of_forall fun q=>by
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hK q) (abs_nonneg _))
  simpa only [integral_const_mul] using he

theorem norm_setIntegral_bounded_coefficient {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (f K : Ω→ℝ) (hf : Integrable (fun q=>|f q|) ν)
    (R : ℝ) (hR : 0 ≤ R) (hK : ∀q,‖K q‖ ≤ R) (S : Set Ω) :
    ‖∫q in S,K q*f q ∂ν‖ ≤ R*(∫q,|f q| ∂ν) := by
  apply (norm_integral_bounded_coefficient (ν.restrict S) f K hf.integrableOn R hR hK).trans
  apply mul_le_mul_of_nonneg_left _ hR
  exact integral_mono_measure ν.restrict_le_self (.of_forall fun q=>abs_nonneg _) hf

theorem norm_integral_min_bounded_coefficient (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (hν : ν.real univ ≤ 1) (φ : C(Paper.Overlap,ℝ)) (K : Paper.Overlap→ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hK : ∀q,‖K q‖ ≤ R) (p : Paper.Overlap) :
    ‖∫q,K q*φ (min p q) ∂ν‖ ≤ R*(|φ p|+∫q,|φ q| ∂ν) := by
  have hi : Integrable (fun q : Paper.Overlap=>|φ p|+|φ q|) ν := by
    apply (integrable_const _).add
    simpa only [Real.norm_eq_abs] using
      (φ.continuous.integrable_of_hasCompactSupport (μ:=ν) (HasCompactSupport.of_compactSpace φ)).norm
  have hpq (q : Paper.Overlap) : |φ (min p q)| ≤ |φ p|+|φ q| := by
    rcases le_total p q with h|h
    · rw [min_eq_left h];linarith [abs_nonneg (φ q)]
    · rw [min_eq_right h];linarith [abs_nonneg (φ p)]
  have he := norm_integral_le_of_norm_le (f:=fun q=>K q*φ (min p q)) (hi.const_mul R) (.of_forall fun q=>by
    rw [norm_mul,Real.norm_eq_abs]
    exact (mul_le_mul (hK q) (hpq q) (abs_nonneg _) hR))
  rw [integral_const_mul,integral_add (integrable_const _) (by
    simpa only [Real.norm_eq_abs] using
      (φ.continuous.integrable_of_hasCompactSupport (μ:=ν) (HasCompactSupport.of_compactSpace φ)).norm),
    integral_const,smul_eq_mul] at he
  apply he.trans
  gcongr
  exact mul_le_of_le_one_left (abs_nonneg _) hν

theorem norm_doubleIntegral_min_bounded_coefficient (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (hν : ν.real univ ≤ 1) (φ : C(Paper.Overlap,ℝ)) (K : Paper.Overlap→Paper.Overlap→ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hK : ∀q r,‖K q r‖ ≤ R) :
    ‖∫q,∫r,K q r*φ (min q r) ∂ν ∂ν‖ ≤ 2*R*(∫q,|φ q| ∂ν) := by
  have hφ : Integrable (fun q : Paper.Overlap=>|φ q|) ν := by
    simpa only [Real.norm_eq_abs] using
      (φ.continuous.integrable_of_hasCompactSupport (μ:=ν) (HasCompactSupport.of_compactSpace φ)).norm
  have hi : Integrable (fun q : Paper.Overlap=>R*(|φ q|+∫r,|φ r| ∂ν)) ν :=
    (hφ.add (integrable_const _)).const_mul R
  have he := norm_integral_le_of_norm_le (f:=fun q=>∫r,K q r*φ (min q r) ∂ν) hi (.of_forall fun q=>
    norm_integral_min_bounded_coefficient ν hν φ (K q) R hR (hK q) q)
  rw [integral_const_mul,integral_add hφ (integrable_const _),integral_const,smul_eq_mul] at he
  apply he.trans
  have hI : 0 ≤ ∫q,|φ q| ∂ν := integral_nonneg fun q=>abs_nonneg _
  have hm := mul_le_mul_of_nonneg_right hν hI
  nlinarith

theorem norm_doubleIntegral_future_bounded_coefficient (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
    (hν : ν.real univ ≤ 1) (φ : C(Paper.Overlap,ℝ)) (K : Paper.Overlap→Paper.Overlap→ℝ)
    (R : ℝ) (hR : 0 ≤ R) (hK : ∀q r,‖K q r‖ ≤ R) :
    ‖∫q,∫r in Ioi q,K q r*φ r ∂ν ∂ν‖ ≤ R*(∫q,|φ q| ∂ν) := by
  have hφ : Integrable (fun q : Paper.Overlap=>|φ q|) ν := by
    simpa only [Real.norm_eq_abs] using
      (φ.continuous.integrable_of_hasCompactSupport (μ:=ν) (HasCompactSupport.of_compactSpace φ)).norm
  have he := norm_integral_le_of_norm_le_const (μ:=ν) (f:=fun q=>∫r in Ioi q,K q r*φ r ∂ν) (.of_forall fun q=>
    norm_setIntegral_bounded_coefficient ν φ (K q) hφ R hR (hK q) (Ioi q))
  apply he.trans
  have hI : 0 ≤ ∫q,|φ q| ∂ν := integral_nonneg fun q=>abs_nonneg _
  simpa only [mul_comm] using mul_le_of_le_one_left (mul_nonneg hR hI) hν

theorem scalar_response_norm_pointwise (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (φ : C(Paper.Overlap,ℝ)) (p : Paper.Overlap) :
    ‖scalarResponseOperator β hβ μ a φ p‖ ≤ 
      6*β^2*scalarResponseKernelBound β*(|φ p|+∫q,|φ q| ∂parisiFreeMeasure μ a) := by
  let ν := parisiFreeMeasure μ a
  let R := scalarResponseKernelBound β
  let I : ℝ := ∫q,|φ q| ∂ν
  have hR : 0 ≤ R := le_trans (by norm_num) (scalarResponseKernelBound_ge_one β)
  have hI : 0 ≤ I := integral_nonneg fun q=>abs_nonneg _
  have hm : ν.real univ ≤ 1 := scalarFreeMeasure_mass_le_one μ a ha
  have hφ : Integrable (fun q : Paper.Overlap=>|φ q|) ν := by
    simpa only [Real.norm_eq_abs] using
      (φ.continuous.integrable_of_hasCompactSupport (μ:=ν) (HasCompactSupport.of_compactSpace φ)).norm
  have hb0 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).1
  have hb1 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.1
  have hb2 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.1
  have hb3 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.2.1
  have hb4 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.2.2.1
  have hb5 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.2.2.2.1
  have hb6 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.2.2.2.2.1
  have hb7 (q r ell : Paper.Overlap) := (scalarResponseKernel_bounds β μ q r ell).2.2.2.2.2.2.2
  let A := (scalarResponseKernel0 β μ p 0 0+2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)*φ p
  let B := ∫r in Ioi p,scalarResponseKernel2 β μ p r 0*φ r ∂ν
  let D := ∫r,scalarResponseKernel3 β μ p r 0*φ (min p r) ∂ν
  let E := ∫r,scalarResponseKernel4 β μ p r 0*φ r ∂ν
  let F := ∫r,parisiCDF μ r*scalarResponseKernel5 β μ p r r*φ r ∂ν
  let G := ∫r,∫ell,scalarResponseKernel6 β μ p r ell*φ (min r ell) ∂ν ∂ν
  let H := ∫r,∫ell in Ioi r,scalarResponseKernel7 β μ p r ell*φ ell ∂ν ∂ν
  have hA : ‖A‖ ≤ 3*R*|φ p| := by
    have hcp : ‖1-parisiCDF μ p‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [parisiCDF_nonneg μ p,parisiCDF_le_one μ p]
    have hb := norm_add_le (scalarResponseKernel0 β μ p 0 0)
      (2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0)
    simp only [norm_mul,Real.norm_ofNat] at hb
    have hbound : ‖scalarResponseKernel0 β μ p 0 0+2*(1-parisiCDF μ p)*scalarResponseKernel1 β μ p p 0‖ ≤ 3*R := by
      have ht := mul_le_mul hcp (hb1 p p 0) (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      nlinarith [hb0 p 0 0]
    change ‖(_)*φ p‖ ≤ 3*R*|φ p|
    rw [norm_mul]
    simpa only [Real.norm_eq_abs] using mul_le_mul_of_nonneg_right hbound (abs_nonneg (φ p))
  have hB : ‖B‖ ≤ R*I := norm_setIntegral_bounded_coefficient ν φ _ hφ R hR (hb2 p · 0) (Ioi p)
  have hD : ‖D‖ ≤ R*(|φ p|+I) := norm_integral_min_bounded_coefficient ν hm φ _ R hR (hb3 p · 0) p
  have hE : ‖E‖ ≤ R*I := norm_integral_bounded_coefficient ν φ _ hφ R hR (hb4 p · 0)
  have hF : ‖F‖ ≤ R*I := by
    apply norm_integral_bounded_coefficient ν φ _ hφ R hR
    intro r
    rw [norm_mul]
    have hcdf : ‖parisiCDF μ r‖ ≤ 1 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (parisiCDF_nonneg μ r)]
      exact parisiCDF_le_one μ r
    exact (mul_le_mul hcdf (hb5 p r r) (norm_nonneg _) (by norm_num)).trans_eq (by ring)
  have hG : ‖G‖ ≤ 2*R*I := norm_doubleIntegral_min_bounded_coefficient ν hm φ _ R hR (hb6 p)
  have hH : ‖H‖ ≤ R*I := norm_doubleIntegral_future_bounded_coefficient ν hm φ _ R hR (hb7 p)
  have h1 := norm_sub_le A B
  have h2 := norm_sub_le (A-B) (2*D)
  have h3 := norm_sub_le (A-B-2*D) E
  have h4 := norm_add_le (A-B-2*D-E) ((1/2:ℝ)*F)
  have h5 := norm_add_le (A-B-2*D-E+(1/2:ℝ)*F) ((1/2:ℝ)*G)
  have h6 := norm_add_le (A-B-2*D-E+(1/2:ℝ)*F+(1/2:ℝ)*G) ((1/2:ℝ)*H)
  simp only [norm_mul,Real.norm_ofNat,norm_div,norm_one] at h2 h4 h5 h6
  have htotal : ‖A-B-2*D-E+(1/2:ℝ)*F+(1/2:ℝ)*G+(1/2:ℝ)*H‖ ≤ 
      6*R*(|φ p|+I) := by nlinarith [abs_nonneg (φ p)]
  rw [scalarResponseOperator_eq_kernels β hβ μ a φ p,norm_mul,Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg β)]
  change β^2*‖A-B-2*D-E+(1/2:ℝ)*F+(1/2:ℝ)*G+(1/2:ℝ)*H‖ ≤ _
  exact (mul_le_mul_of_nonneg_left htotal (sq_nonneg β)).trans_eq (by dsimp only [R,I,ν];ring)

end QuantitativeFollowup
