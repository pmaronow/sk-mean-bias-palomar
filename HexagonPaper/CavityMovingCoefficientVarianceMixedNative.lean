module
public import HexagonPaper.CavityMovingCoefficientVarianceResponseGradient
public import FourPapersCommon.JointDerivativeContinuity
public import QuantitativeFollowup.ParameterSpatialInterchange

@[expose] public section

/-! Joint continuity of the genuine spatial derivative of the last
coefficient response. A uniform differential modulus converts actual
value continuity into derivative continuity without a mixed receiver. -/
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

theorem cavityMoving_continuous_fderiv_of_uniform_differential_modulus
    {A E F : Type*} [TopologicalSpace A]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : A×E→F) (hf : Continuous f) (hs : ∀a,ContDiff ℝ 1 (fun x=>f (a,x)))
    (C : ℝ) (hC : 0≤C)
    (hL : ∀a,LipschitzWith C.toNNReal (fderiv ℝ (fun x=>f (a,x)))) :
    Continuous (fun z : A×E=>fderiv ℝ (fun y=>f (z.1,y)) z.2) := by
  apply continuous_clm_apply.mpr
  intro v
  let δ:=fun j : ℕ=>((j+1 : ℕ) : ℝ)⁻¹
  let F:=fun j (z : A×E)=>(δ j)⁻¹ • (f (z.1,z.2+δ j • v)-f z)
  have hδ (j : ℕ) : 0<δ j := by dsimp only [δ]; positivity
  have hc (j : ℕ) : Continuous (F j) := by
    unfold F
    exact ((hf.comp (continuous_fst.prodMk (continuous_snd.add continuous_const))).sub hf).const_smul _
  have hb (j : ℕ) (z : A×E) :
      ‖F j z-fderiv ℝ (fun y=>f (z.1,y)) z.2 v‖≤C*δ j*‖v‖^2 := by
    have hh:=firstTaylor_remainder_Banach (fun y=>f (z.1,y)) (hs z.1).differentiable_one
      C.toNNReal (hL z.1) z.2 (δ j • v)
    rw [Real.coe_toNNReal _ hC,norm_smul,Real.norm_eq_abs,abs_of_pos (hδ j)] at hh
    have he : F j z-fderiv ℝ (fun y=>f (z.1,y)) z.2 v=
        (δ j)⁻¹ • (f (z.1,z.2+δ j • v)-f z-fderiv ℝ (fun y=>f (z.1,y)) z.2 (δ j • v)) := by
      dsimp only [F]
      simp only [smul_sub,map_smul,smul_smul,inv_mul_cancel₀ (hδ j).ne',one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hδ j))]
    refine (mul_le_mul_of_nonneg_left hh (inv_pos.mpr (hδ j)).le).trans_eq ?_
    field_simp
  have htδ : Tendsto δ atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hu : TendstoUniformly F (fun z : A×E=>fderiv ℝ (fun y=>f (z.1,y)) z.2 v) atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have ht : Tendsto (fun j=>C*δ j*‖v‖^2) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using (htδ.const_mul C).mul_const (‖v‖^2)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with j hj
    intro z
    rw [dist_comm,dist_eq_norm]
    exact (hb j z).trans_lt hj
  exact hu.continuous (Eventually.of_forall hc).frequently

theorem cavityNativeVarianceResponse_fderiv_coefficient_field_joint_continuous
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (i : Fin n)
    (g : AnisotropicDisorder n) (q : Paper.Overlap) :
    Continuous (fun z : {b : ℝ // 0<b}×Field n=>
      fderiv ℝ (fun y=>anisotropicRestartVarianceResponse
        (anisotropicReplaceVariance D i z.1.val) μ g q y i) z.2) := by
  let C : ℝ:=(1/2 : ℝ)*(31*‖cavityCoordinateFeature i‖^2*‖anisotropicRestartFieldEnergyMap D‖^2)
  have hC : 0≤C := by dsimp only [C]; positivity
  apply cavityMoving_continuous_fderiv_of_uniform_differential_modulus
    (fun z : {b : ℝ // 0<b}×Field n=>anisotropicRestartVarianceResponse
      (anisotropicReplaceVariance D i z.1.val) μ g q z.2 i)
    (cavityNativeVarianceResponse_coefficient_field_joint_continuous D μ i g q)
    (fun b=>cavityNativeVarianceResponse_contDiff_one_field (anisotropicReplaceVariance D i b.val) μ g q i)
    C hC
  intro b
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [dist_eq_norm,dist_eq_norm,Real.coe_toNNReal _ hC]
  simpa only [C,anisotropicRestartFieldEnergyMap,anisotropicReplaceVariance_energyMap] using
    cavityNativeVarianceResponse_fderiv_field_difference_bound (anisotropicReplaceVariance D i b.val)
      μ g q i x y

end HexagonPaper
