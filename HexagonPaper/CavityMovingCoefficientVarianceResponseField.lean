module
public import HexagonPaper.CavityMovingCoefficientVarianceResponseContinuity
public import HexagonPaper.CavityFixedRowJetMeasurableSections
public import QuantitativePaper.SmoothIntegral

@[expose] public section

/-! Genuine spatial C1 regularity of the native variance response. The
Stieltjes integrand is the actual restart spin square; all measurability
and derivative bounds are discharged from its native field theorem. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology ContDiff NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
variable {n : ℕ}

def cavityMovingVarianceResponseFieldIntegrand (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n) (q : Paper.Overlap)
    (i : Fin n) (x : Field n) (r : Paper.Overlap) : ℝ :=
  max 0 ((r : ℝ)-(q : ℝ))*anisotropicRestartSpinSquare D μ g q x i (max q r)

theorem cavityMovingVarianceResponseFieldIntegrand_contDiff_one
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (r : Paper.Overlap) :
    ContDiff ℝ 1 (fun x=>cavityMovingVarianceResponseFieldIntegrand D μ g q i x r) :=
  contDiff_const.mul (contDiff_anisotropicRestartSpinSquare_field D μ g q (max q r) (le_max_left _ _) i)

theorem cavityMovingVarianceResponseFieldIntegrand_measurable
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) :
    Measurable (cavityMovingVarianceResponseFieldIntegrand D μ g q i x) :=
  (measurable_const.max (measurable_subtype_coe.sub_const _)).mul
    ((measurable_anisotropicRestartSpinSquare D μ g q x i).comp (measurable_const.max measurable_id))

theorem cavityMovingVarianceResponseFieldIntegrand_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) (r : Paper.Overlap) :
    ‖cavityMovingVarianceResponseFieldIntegrand D μ g q i x r‖≤1 := by
  have hs:=anisotropicRestartSpinSquare_mem_Icc D μ g q x i (max q r)
  unfold cavityMovingVarianceResponseFieldIntegrand
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (le_max_left _ _) hs.1)]
  exact (mul_le_of_le_one_right (le_max_left _ _) hs.2).trans
    (max_le (by norm_num) (by linarith [r.property.2,q.property.1]))

theorem cavityMovingVarianceResponseFieldIntegrand_fderiv_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) (x : Field n) (r : Paper.Overlap) :
    ‖fderiv ℝ (fun y=>cavityMovingVarianceResponseFieldIntegrand D μ g q i y r) x‖≤
      4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖ := by
  let K : ℝ≥0:=4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊
  have hL : LipschitzWith K (fun y=>cavityMovingVarianceResponseFieldIntegrand D μ g q i y r) := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hh:=(anisotropicRestartSpinSquare_field_lipschitz D μ g q (max q r)
      (le_max_left _ _) i).dist_le_mul y z
    rw [dist_eq_norm,dist_eq_norm] at hh ⊢
    unfold cavityMovingVarianceResponseFieldIntegrand
    rw [←mul_sub,norm_mul,Real.norm_of_nonneg (le_max_left _ _)]
    apply (mul_le_mul_of_nonneg_left hh (le_max_left _ _)).trans
    have hc : max 0 ((r : ℝ)-(q : ℝ))≤1 :=
      max_le (by norm_num) (by linarith [r.property.2,q.property.1])
    exact (mul_le_mul_of_nonneg_right hc (mul_nonneg K.coe_nonneg (norm_nonneg _))).trans_eq (one_mul _)
  simpa [K] using norm_fderiv_le_of_lipschitz ℝ hL

theorem cavityMovingVarianceResponseFieldIntegral_contDiff_one
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) :
    ContDiff ℝ 1 (fun x=>∫r,cavityMovingVarianceResponseFieldIntegrand D μ g q i x r
      ∂(μ : Measure Paper.Overlap)) := by
  let F:=cavityMovingVarianceResponseFieldIntegrand D μ g q i
  let K : ℝ:=4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖
  have hs (r : Paper.Overlap) : ContDiff ℝ 1 (fun x=>F x r) :=
    cavityMovingVarianceResponseFieldIntegrand_contDiff_one D μ g q i r
  have hm : Measurable (fun z : Paper.Overlap×Field n=>F z.2 z.1) :=
    measurable_cavityFiniteFunctional_sections _
      (cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i) (fun r=>(hs r).continuous)
  have hDm : Measurable (fun z : Paper.Overlap×Field n=>fderiv ℝ (fun y=>F y z.1) z.2) :=
    measurable_cavityFiniteFDeriv _ hm (fun r=>(hs r).differentiable_one)
  have hDa (x : Field n) : AEStronglyMeasurable (fun r=>fderiv ℝ (fun y=>F y r) x)
      (μ : Measure Paper.Overlap) :=
    (hDm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hD (x : Field n) : HasFDerivAt (fun y=>∫r,F y r∂(μ : Measure Paper.Overlap))
      (∫r,fderiv ℝ (fun y=>F y r) x∂(μ : Measure Paper.Overlap)) x := by
    apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s:=univ) univ_mem
      (.of_forall fun y=>(cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i y).aestronglyMeasurable)
      (Integrable.of_bound (cavityMovingVarianceResponseFieldIntegrand_measurable D μ g q i x).aestronglyMeasurable
        1 (.of_forall fun r=>cavityMovingVarianceResponseFieldIntegrand_bound D μ g q i x r))
      (hDa x) (bound:=fun _=>K)
    · exact .of_forall fun r y _=>cavityMovingVarianceResponseFieldIntegrand_fderiv_bound D μ g q i y r
    · exact integrable_const K
    · exact .of_forall fun r y _=>((hs r).differentiable_one y).hasFDerivAt
  have hc : Continuous (fun x=>∫r,fderiv ℝ (fun y=>F y r) x∂(μ : Measure Paper.Overlap)) := by
    apply continuous_of_dominated (bound:=fun _=>K)
    · exact hDa
    · exact fun x=>.of_forall fun r=>cavityMovingVarianceResponseFieldIntegrand_fderiv_bound D μ g q i x r
    · exact integrable_const K
    · exact .of_forall fun r=>(hs r).continuous_fderiv (by norm_num)
  apply contDiff_succ_iff_hasFDerivAt.mpr
  refine ⟨_,?_,hD⟩
  change ContDiff ℝ 0 _
  exact contDiff_zero.mpr hc

theorem cavityNativeVarianceResponse_contDiff_one_field
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (g : AnisotropicDisorder n)
    (q : Paper.Overlap) (i : Fin n) :
    ContDiff ℝ 1 (fun x=>anisotropicRestartVarianceResponse D μ g q x i) := by
  have he : (fun x=>anisotropicRestartVarianceResponse D μ g q x i)=
      (fun x=>(1/2 : ℝ)*(1-(q : ℝ)-∫r,cavityMovingVarianceResponseFieldIntegrand D μ g q i x r
        ∂(μ : Measure Paper.Overlap))) := by
    funext x
    unfold anisotropicRestartVarianceResponse
    congr 2
    apply integral_congr_ae
    exact .of_forall fun r=>by
      by_cases hqr : q≤r
      · simp only [cavityMovingVarianceResponseFieldIntegrand,max_eq_right hqr]
      · have hz : max 0 ((r : ℝ)-(q : ℝ))=0 :=
          max_eq_left (sub_nonpos.mpr (show (r : ℝ)≤(q : ℝ) from le_of_not_ge hqr))
        simp only [cavityMovingVarianceResponseFieldIntegrand,hz,zero_mul]
  rw [he]
  exact contDiff_const.mul (contDiff_const.sub (cavityMovingVarianceResponseFieldIntegral_contDiff_one D μ g q i))

end HexagonPaper
