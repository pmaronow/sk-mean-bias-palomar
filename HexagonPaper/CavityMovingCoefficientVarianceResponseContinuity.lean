module
public import QuantitativeFollowup.AnisotropicVarianceDerivative
public import QuantitativeFollowup.SupportingNativeRestartFieldDerivativeLipschitz
public import FourPapersCommon.MovingDerivativeLimit

@[expose] public section

/-! The true native last-coefficient response is continuous, obtained
from the genuine moving finite response limit rather than an assumed
regularity of the limiting derivative. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem cavityMoving_continuousAt_of_all_moving_limits
    (F : ℕ→ℝ→ℝ) (f : ℝ→ℝ) (b : ℝ) (hb : 0<b)
    (hpoint : ∀u,0<u→Tendsto (fun j=>F j u) atTop (𝓝 (f u)))
    (hmoving : ∀u : ℕ→ℝ,Tendsto u atTop (𝓝 b)→
      Tendsto (fun j=>F j (u j)) atTop (𝓝 (f b))) :
    ContinuousAt f b := by
  have hprod:=tendsto_prod_of_all_moving_sequences F b (f b) hmoving
  change Tendsto f (𝓝 b) (𝓝 (f b))
  rw [Metric.tendsto_nhds] at hprod ⊢
  intro ε hε
  obtain ⟨s,hs,t,ht,h⟩:=eventually_prod_iff.mp (hprod (ε/2) (half_pos hε))
  filter_upwards [ht,Ioi_mem_nhds hb] with u hu hupos
  have hdist : dist (f u) (f b)≤ε/2 := by
    apply le_of_tendsto ((hpoint u hupos).dist tendsto_const_nhds)
    filter_upwards [hs] with j hj
    exact (h hj hu).le
  exact hdist.trans_lt (half_lt_self hε)

theorem cavityNativeVarianceResponse_continuousAt_coefficient
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n)
    (b : ℝ) (hb : 0<b) :
    ContinuousAt (fun u=>anisotropicRestartVarianceResponse
      (anisotropicReplaceVariance D i u) μ g q x i) b := by
  apply cavityMoving_continuousAt_of_all_moving_limits
    (fun j u=>anisotropicFiniteTailVarianceResponse (anisotropicReplaceVariance D i u)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q
      (anisotropicDisorderInjection n g+anisotropicFieldInjection n x) i) _ b hb
  · intro u hu
    exact tendsto_anisotropicVarianceFiniteTailResponse D μ i hu tendsto_const_nhds g q x
  · intro u hu
    exact tendsto_anisotropicVarianceFiniteTailResponse D μ i hb hu g q x

theorem cavityNativeVarianceResponse_continuous_coefficient
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (x : Field n) :
    Continuous (fun b : {b : ℝ // 0<b}=>anisotropicRestartVarianceResponse
      (anisotropicReplaceVariance D i b.val) μ g q x i) := by
  rw [continuous_iff_continuousAt]
  intro b
  exact (cavityNativeVarianceResponse_continuousAt_coefficient D μ i g q x b.val b.property).comp
    continuous_subtype_val.continuousAt

theorem cavityNativeVarianceResponse_field_difference_bound
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) (i : Fin n) (x y : Field n) :
    ‖anisotropicRestartVarianceResponse D μ g q x i-
      anisotropicRestartVarianceResponse D μ g q y i‖≤
      (1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖)*‖x-y‖ := by
  let K : ℝ≥0:=4*‖cavityCoordinateFeature i‖₊^2*‖anisotropicRestartFieldEnergyMap D‖₊
  let F:=fun (x : Field n) (r : Paper.Overlap)=>max 0 ((r : ℝ)-(q : ℝ))*
    anisotropicRestartSpinSquare D μ g q x i r
  have hcoef (r : Paper.Overlap) : max 0 ((r : ℝ)-(q : ℝ))≤1 :=
    max_le (by norm_num) (by linarith [r.property.2,q.property.1])
  have hm (x : Field n) : Measurable (F x) :=
    (measurable_const.max (measurable_subtype_coe.sub_const _)).mul
      (measurable_anisotropicRestartSpinSquare D μ g q x i)
  have hi (x : Field n) : Integrable (F x) (μ : Measure Paper.Overlap) :=
    Integrable.of_bound (hm x).aestronglyMeasurable 1 (.of_forall fun r=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (le_max_left _ _)
        (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).1)]
      exact (mul_le_of_le_one_right (le_max_left _ _)
        (anisotropicRestartSpinSquare_mem_Icc D μ g q x i r).2).trans (hcoef r))
  have hbound (r : Paper.Overlap) : ‖F x r-F y r‖≤(K : ℝ)*‖x-y‖ := by
    by_cases hqr : q≤r
    · have hs:=(anisotropicRestartSpinSquare_field_lipschitz D μ g q r hqr i).dist_le_mul x y
      rw [dist_eq_norm,dist_eq_norm] at hs
      rw [←mul_sub,norm_mul,Real.norm_of_nonneg (le_max_left _ _)]
      exact (mul_le_mul_of_nonneg_left hs (le_max_left _ _)).trans
        ((mul_le_mul_of_nonneg_right (hcoef r) (mul_nonneg K.coe_nonneg (norm_nonneg _))).trans_eq (one_mul _))
    · have hz : max 0 ((r : ℝ)-(q : ℝ))=0 :=
        max_eq_left (sub_nonpos.mpr (show (r : ℝ)≤(q : ℝ) from le_of_not_ge hqr))
      simp only [F,hz,zero_mul,sub_self,norm_zero]
      positivity
  have hI : ‖∫r,F x r-F y r∂(μ : Measure Paper.Overlap)‖≤(K : ℝ)*‖x-y‖ := by
    simpa only [probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=(μ : Measure Paper.Overlap)) (.of_forall hbound)
  have he : anisotropicRestartVarianceResponse D μ g q x i-
      anisotropicRestartVarianceResponse D μ g q y i=
      -(1/2 : ℝ)*(∫r,F x r-F y r∂(μ : Measure Paper.Overlap)) := by
    rw [integral_sub (hi x) (hi y)]
    unfold anisotropicRestartVarianceResponse F
    ring
  rw [he,norm_mul]
  norm_num only [norm_neg,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<1/2)]
  exact (mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ)≤1/2)).trans_eq
    (by simp only [K,NNReal.coe_mul,NNReal.coe_pow,coe_nnnorm]; norm_num; ring)

theorem cavityNativeVarianceResponse_coefficient_field_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i z.1.val) μ g q z.2 i) := by
  rw [continuous_iff_continuousAt]
  intro z0
  let R:=fun (b : {b : ℝ // 0<b}) (x : Field n)=>
    anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i b.val) μ g q x i
  let K : ℝ:=(1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hR : Continuous (fun z : {b : ℝ // 0<b}×Field n=>R z.1 z0.2) :=
    (cavityNativeVarianceResponse_continuous_coefficient D μ i g q z0.2).comp continuous_fst
  have hx : Tendsto (fun z : {b : ℝ // 0<b}×Field n=>K*‖z.2-z0.2‖) (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : {b : ℝ // 0<b}×Field n=>K*‖z.2-z0.2‖) :=
      continuous_const.mul ((continuous_snd.sub continuous_const).norm)
    simpa only [sub_self,norm_zero,mul_zero] using
      hc.tendsto z0
  have hr : Tendsto (fun z : {b : ℝ // 0<b}×Field n=>‖R z.1 z0.2-R z0.1 z0.2‖) (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : {b : ℝ // 0<b}×Field n=>‖R z.1 z0.2-R z0.1 z0.2‖) :=
      (hR.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto z0
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) _ (by simpa only [zero_add] using hx.add hr)
  intro z
  have hd : ‖R z.1 z.2-R z.1 z0.2‖≤K*‖z.2-z0.2‖ := by
    simpa only [R,K,anisotropicRestartFieldEnergyMap,anisotropicReplaceVariance_energyMap] using
      cavityNativeVarianceResponse_field_difference_bound (anisotropicReplaceVariance D i z.1.val)
        μ g q i z.2 z0.2
  have he : R z.1 z.2-R z0.1 z0.2=
      (R z.1 z.2-R z.1 z0.2)+(R z.1 z0.2-R z0.1 z0.2) := by ring
  change ‖R z.1 z.2-R z0.1 z0.2‖≤_
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hd le_rfl)

end HexagonPaper
