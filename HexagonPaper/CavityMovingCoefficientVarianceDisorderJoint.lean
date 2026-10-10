module
public import HexagonPaper.CavityMovingCoefficientVarianceDisorderContinuity

@[expose] public section

/-! The genuine variance response and its actual field differential are
jointly continuous in positive coefficient, disorder, and initial field. -/
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

theorem cavityNativeVarianceResponse_coefficient_disorder_field_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n) (q : Paper.Overlap) :
    Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i z.1.1.val) μ z.1.2 q z.2 i) := by
  rw [continuous_iff_continuousAt]
  intro z0
  let R:=fun (b : {b : ℝ // 0<b}) (g : AnisotropicDisorder n) (x : Field n)=>
    anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i b.val) μ g q x i
  let P:=fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
    anisotropicDisorderInjection n z.1.2+anisotropicFieldInjection n z.2
  let K : ℝ:=(1/2 : ℝ)*(4*‖cavityCoordinateFeature i‖^2*‖anisotropicEnergyMap D‖)
  have hP : Continuous P :=
    ((anisotropicDisorderInjection n).continuous.comp continuous_fst.snd).add
      ((anisotropicFieldInjection n).continuous.comp continuous_snd)
  have hR : Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>R z.1.1 z0.1.2 z0.2) := by
    have h:= (cavityNativeVarianceResponse_continuous_coefficient D μ i z0.1.2 q z0.2).comp
      (show Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>z.1.1) from continuous_fst.fst)
    dsimp only [Function.comp_def] at h
    exact h
  have hp : Tendsto (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>K*‖P z-P z0‖)
      (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>K*‖P z-P z0‖) :=
      continuous_const.mul ((hP.sub continuous_const).norm)
    simpa only [sub_self,norm_zero,mul_zero] using hc.tendsto z0
  have hr : Tendsto (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      ‖R z.1.1 z0.1.2 z0.2-R z0.1.1 z0.1.2 z0.2‖) (𝓝 z0) (𝓝 0) := by
    have hc : Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      ‖R z.1.1 z0.1.2 z0.2-R z0.1.1 z0.1.2 z0.2‖) := (hR.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto z0
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _=>norm_nonneg _) _ (by simpa only [zero_add] using hp.add hr)
  intro z
  have hd : ‖R z.1.1 z.1.2 z.2-R z.1.1 z0.1.2 z0.2‖≤K*‖P z-P z0‖ := by
    simpa only [R,P,K,anisotropicReplaceVariance_energyMap] using
      cavityNativeVarianceResponse_parameter_difference_bound (anisotropicReplaceVariance D i z.1.1.val)
        μ q i z.1.2 z0.1.2 z.2 z0.2
  change ‖R z.1.1 z.1.2 z.2-R z0.1.1 z0.1.2 z0.2‖≤_
  rw [show R z.1.1 z.1.2 z.2-R z0.1.1 z0.1.2 z0.2=
    (R z.1.1 z.1.2 z.2-R z.1.1 z0.1.2 z0.2)+(R z.1.1 z0.1.2 z0.2-R z0.1.1 z0.1.2 z0.2) by ring]
  exact (norm_add_le _ _).trans (add_le_add hd le_rfl)

theorem cavityNativeVarianceResponse_fderiv_coefficient_disorder_field_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n) (q : Paper.Overlap) :
    Continuous (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      fderiv ℝ (fun y=>anisotropicRestartVarianceResponse
        (anisotropicReplaceVariance D i z.1.1.val) μ z.1.2 q y i) z.2) := by
  let C : ℝ:=(1/2 : ℝ)*(31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2)
  have hC : 0≤C := by dsimp only [C]; positivity
  apply cavityMoving_continuous_fderiv_of_uniform_differential_modulus
    (fun z : ({b : ℝ // 0<b}×AnisotropicDisorder n)×Field n=>
      anisotropicRestartVarianceResponse (anisotropicReplaceVariance D i z.1.1.val) μ z.1.2 q z.2 i)
    (cavityNativeVarianceResponse_coefficient_disorder_field_joint_continuous D μ i q)
    (fun z=>cavityNativeVarianceResponse_contDiff_one_field (anisotropicReplaceVariance D i z.1.val) μ z.2 q i)
    C hC
  intro z
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hC]
  simpa only [C,anisotropicRestartFieldEnergyMap,anisotropicReplaceVariance_energyMap] using
    cavityNativeVarianceResponse_fderiv_field_difference_bound (anisotropicReplaceVariance D i z.1.val)
      μ z.2 q i x y

end HexagonPaper
