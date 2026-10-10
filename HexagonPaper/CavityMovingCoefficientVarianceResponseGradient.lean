module
public import HexagonPaper.CavityMovingCoefficientVarianceResponseField

@[expose] public section

/-! The actual field gradient of the native variance response has a
uniform Lipschitz modulus. This is inherited by integration from the
genuine native restart-square differential, independent of the profile. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

theorem cavityMovingVarianceResponseFieldIntegral_hasFDerivAt
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) :
    HasFDerivAt (fun y=>∫r,cavityMovingVarianceResponseFieldIntegrand D μ g q i y r
      ∂(μ : Measure Paper.Overlap))
      (∫r,fderiv ℝ (fun y=>cavityMovingVarianceResponseFieldIntegrand D μ g q i y r) x
        ∂(μ : Measure Paper.Overlap)) x := by
  let F:=cavityMovingVarianceResponseFieldIntegrand D μ g q i
  let K : ℝ:=4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖
  have hs (r : Paper.Overlap) : ContDiff ℝ 1 (fun x=>F x r) :=
    cavityMovingVarianceResponseFieldIntegrand_contDiff_one D μ g q i r
  have hm : Measurable (fun z : Paper.Overlap×Field n=>F z.2 z.1) :=
    measurable_cavityFiniteFunctional_sections _
      (cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i) (fun r=>(hs r).continuous)
  have hDm : Measurable (fun z : Paper.Overlap×Field n=>fderiv ℝ (fun y=>F y z.1) z.2) :=
    measurable_cavityFiniteFDeriv _ hm (fun r=>(hs r).differentiable_one)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=univ) univ_mem
    (.of_forall fun y=>(cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i y).aestronglyMeasurable)
    (Integrable.of_bound (cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i x).aestronglyMeasurable
      1 (.of_forall fun r=>cavityMovingVarianceResponseFieldIntegrand_bound D μ g q i x r))
    ((hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) (bound:=fun _=>K)
  · exact .of_forall fun r y _=>cavityMovingVarianceResponseFieldIntegrand_fderiv_bound D μ g q i y r
  · exact integrable_const K
  · exact .of_forall fun r y _=>((hs r).differentiable_one y).hasFDerivAt

theorem cavityNativeVarianceResponse_eq_clamped_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) :
    anisotropicRestartVarianceResponse D μ g q x i=
      (1/2 : ℝ)*(1-(q : ℝ)-∫r,cavityMovingVarianceResponseFieldIntegrand D μ g q i x r
        ∂(μ : Measure Paper.Overlap)) := by
  unfold anisotropicRestartVarianceResponse
  congr 2
  apply integral_congr_ae
  exact .of_forall fun r=>by
    by_cases hqr : q≤r
    · simp only [cavityMovingVarianceResponseFieldIntegrand,max_eq_right hqr]
    · have hz : max 0 ((r : ℝ)-(q : ℝ))=0 :=
        max_eq_left (sub_nonpos.mpr (show (r : ℝ)≤(q : ℝ) from le_of_not_ge hqr))
      simp only [cavityMovingVarianceResponseFieldIntegrand,hz,zero_mul]

theorem cavityNativeVarianceResponse_fderiv_field_eq_integral
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) :
    fderiv ℝ (fun y=>anisotropicRestartVarianceResponse D μ g q y i) x=
      -(1/2 : ℝ) • (∫r,fderiv ℝ (fun y=>cavityMovingVarianceResponseFieldIntegrand D μ g q i y r) x
        ∂(μ : Measure Paper.Overlap)) := by
  have hd:=((cavityMovingVarianceResponseFieldIntegral_hasFDerivAt D μ g q i x).const_sub
    (1-(q : ℝ))).const_mul (1/2 : ℝ)
  have he : (fun y=>anisotropicRestartVarianceResponse D μ g q y i)=
      (fun y=>(1/2 : ℝ)*(1-(q : ℝ)-∫r,cavityMovingVarianceResponseFieldIntegrand D μ g q i y r
        ∂(μ : Measure Paper.Overlap))) :=
    funext (cavityNativeVarianceResponse_eq_clamped_integral D μ g q i)
  rw [he]
  simpa only [smul_neg,neg_smul] using hd.fderiv

theorem cavityMovingVarianceResponseFieldIntegrand_fderiv_difference_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x y : Field n) (r : Paper.Overlap) :
    ‖fderiv ℝ (fun z=>cavityMovingVarianceResponseFieldIntegrand D μ g q i z r) x-
      fderiv ℝ (fun z=>cavityMovingVarianceResponseFieldIntegrand D μ g q i z r) y‖≤
      (31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2)*‖x-y‖ := by
  let K : ℝ≥0:=31*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊^2
  have hs:=contDiff_anisotropicRestartSpinSquare_field D μ g q (max q r) (le_max_left _ _) i
  have he (z : Field n) :
      fderiv ℝ (fun z=>cavityMovingVarianceResponseFieldIntegrand D μ g q i z r) z=
      max 0 ((r : ℝ)-(q : ℝ)) • fderiv ℝ (fun z=>anisotropicRestartSpinSquare D μ g q z i (max q r)) z := by
    exact (((hs.differentiable_one z).hasFDerivAt).const_mul _).fderiv
  rw [he x,he y,←smul_sub,norm_smul,Real.norm_of_nonneg (le_max_left _ _)]
  have hd:=(anisotropicRestartSpinSquare_field_differential_lipschitz D μ g q (max q r)
    (le_max_left _ _) i).dist_le_mul x y
  rw [dist_eq_norm,dist_eq_norm] at hd
  have hc : max 0 ((r : ℝ)-(q : ℝ))≤1 :=
    max_le (by norm_num) (by linarith [r.property.2,q.property.1])
  apply (mul_le_mul_of_nonneg_left hd (le_max_left _ _)).trans
  have hK : (K : ℝ)=31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2 := by simp [K]
  exact ((mul_le_mul_of_nonneg_right hc (mul_nonneg K.coe_nonneg (norm_nonneg _))).trans_eq (one_mul _)).trans_eq
    (by rw [hK])

theorem cavityNativeVarianceResponse_fderiv_field_difference_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x y : Field n) :
    ‖fderiv ℝ (fun z=>anisotropicRestartVarianceResponse D μ g q z i) x-
      fderiv ℝ (fun z=>anisotropicRestartVarianceResponse D μ g q z i) y‖≤
      (1/2 : ℝ)*(31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2)*‖x-y‖ := by
  let F:=cavityMovingVarianceResponseFieldIntegrand D μ g q i
  let K : ℝ:=4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖
  let J : ℝ:=31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2
  have hm : Measurable (fun z : Paper.Overlap×Field n=>F z.2 z.1) :=
    measurable_cavityFiniteFunctional_sections _
      (cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i)
      (fun r=>(cavityMovingVarianceResponseFieldIntegrand_contDiff_one D μ g q i r).continuous)
  have hDm : Measurable (fun z : Paper.Overlap×Field n=>fderiv ℝ (fun y=>F y z.1) z.2) :=
    measurable_cavityFiniteFDeriv _ hm
      (fun r=>(cavityMovingVarianceResponseFieldIntegrand_contDiff_one D μ g q i r).differentiable_one)
  have hi (z : Field n) : Integrable (fun r=>fderiv ℝ (fun y=>F y r) z) (μ : Measure Paper.Overlap) :=
    Integrable.of_bound ((hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      K (.of_forall fun r=>cavityMovingVarianceResponseFieldIntegrand_fderiv_bound D μ g q i z r)
  rw [cavityNativeVarianceResponse_fderiv_field_eq_integral D μ g q i x,
    cavityNativeVarianceResponse_fderiv_field_eq_integral D μ g q i y,←smul_sub,←integral_sub (hi x) (hi y),norm_smul]
  have hB : ‖∫r,(fderiv ℝ (fun z=>F z r) x-fderiv ℝ (fun z=>F z r) y)∂(μ : Measure Paper.Overlap)‖≤J*‖x-y‖ := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=(μ : Measure Paper.Overlap)) (.of_forall fun r=>
        cavityMovingVarianceResponseFieldIntegrand_fderiv_difference_bound D μ g q i x y r)
  norm_num only [norm_neg,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hB (by norm_num : (0 : ℝ)≤1/2)).trans_eq (by ring)

end HexagonPaper
