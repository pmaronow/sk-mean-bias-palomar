module
public import HexagonPaper.CavityFixedRowExpansionFutureContractions
public import HexagonPaper.CavityFixedRowExpansionPairingData
public import QuantitativeFollowup.FollowupCavityCppZeroResponseLastEvaluation

@[expose] public section

/-! Literal complete last-coordinate response and T1 signed residual for
all probability profiles. The actual native marked laws supply the moments;
strict-future and two-time Fubini retain every profile atom. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup FRSB
namespace HexagonPaper
open SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem cavityLast_integral_combination {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F0 F1 F2 F3 F4 : Ω→ℝ) (c : ℝ)
    (h0 : Integrable F0 P) (h1 : Integrable F1 P) (h2 : Integrable F2 P)
    (h3 : Integrable F3 P) (h4 : Integrable F4 P) :
    (∫z,F0 z-2*c*F1 z-F2 z+2*F3 z-2*F4 z ∂P)=
      (∫z,F0 z ∂P)-2*c*(∫z,F1 z ∂P)-(∫z,F2 z ∂P)+
        2*(∫z,F3 z ∂P)-2*(∫z,F4 z ∂P) :=by
  have hi01 : Integrable (fun z=>F0 z-2*c*F1 z) P:=h0.sub (h1.const_mul (2*c))
  have hi012 : Integrable (fun z=>F0 z-2*c*F1 z-F2 z) P:=hi01.sub h2
  have hi0123 : Integrable (fun z=>F0 z-2*c*F1 z-F2 z+2*F3 z) P:=hi012.add (h3.const_mul 2)
  rw [integral_sub hi0123 (h4.const_mul 2),
    integral_add hi012 (h3.const_mul 2),
    integral_sub hi01 h2,
    integral_sub h0 (h1.const_mul (2*c)),integral_const_mul,integral_const_mul,integral_const_mul]

theorem cavityFixedRowLastResponseIntegrand_data_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    Integrable (fun z=>cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) ∧
    (∫z,cavityZeroLastResponseIntegrand μ n β ρ hβ hρ a p z
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      (scalarResponseKernel0 B μ p p 0+
        2*(1-Paper.parisiCDF μ p)*scalarResponseKernel1 B μ p p 0)*
        cavityRestCovarianceColumn D μ a p p-
      (∫r,if p<r then cavityRestCovarianceColumn D μ a p r*
        scalarResponseKernel2 B μ p r 0 else 0 ∂parisiFreeMeasure μ a)-
      2*(∫r,cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      cavitySignedResponseT1 D μ a B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' p :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let xs:=fun z=>(cavityZeroMarkedSampleSplit n z).2
  let xr:=fun z=>(cavityZeroMarkedSampleSplit n z).1
  let A:=fun z=>cavitySignedResponseCenteredSelfOverlap D μ a p (xr z).1
  let F0:=fun z=>cavitySignedResponseSelfOverlap D μ p (xr z).1*A z*
    scalarResponseSample 0 B μ p p 0 (xs z)
  let F1:=fun z=>cavitySignedResponseSelfOverlap D μ p (xr z).1*A z*
    scalarResponseSample 1 B μ p p 0 (xs z)
  let F2:=fun z=>∫r,if p<r then cavityRestFutureSquare D μ p r (xr z).1*A z*
    scalarResponseSample 2 B μ p r 0 (xs z) else 0 ∂parisiFreeMeasure μ a
  let G:=fun z : Paper.BrownianSample×Bool=>M B μ p z.1*C B μ p z.1*Paper.spinSign z.2
  let F3:=fun z=>(cavityRestTerminalMeanPairing D μ p (xr z)*A z)*G (xs z)
  let F4:=fun z=>∫r,cavityRestTwoTimeMeanPairing D μ p r (xr z).1*A z*
    scalarResponseSample 3 B μ p r 0 (xs z) ∂parisiFreeMeasure μ a
  have harg : Measurable (fun z : AnisotropicDisorderBrownianSample n=>(p,z)) :=
    measurable_const.prodMk measurable_id
  have hself : Measurable (cavitySignedResponseSelfOverlap D μ p) :=by
    simpa only [Function.comp_def,Function.uncurry_def] using
      (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp harg
  have hi0 : Integrable F0 P:=integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
    (fun z=>cavitySignedResponseSelfOverlap D μ p z.1) (hself.comp measurable_fst)
    1 zero_le_one (fun z=>norm_cavitySignedResponseSelfOverlap_le D μ p z.1) 0 p 0
  have hi1 : Integrable F1 P:=integrable_cavityZeroMarked_rest_centered_sample μ n β ρ hβ hρ a p
    (fun z=>cavitySignedResponseSelfOverlap D μ p z.1) (hself.comp measurable_fst)
    1 zero_le_one (fun z=>norm_cavitySignedResponseSelfOverlap_le D μ p z.1) 1 p 0
  have hi2 : Integrable F2 P:=
    (cavityFixedRowMarked_strict_future_kernel2_data_all_profiles μ n β ρ hβ hρ a p).1
  have hG : Measurable G:=
    (((measurable_M B μ p p.property).comp measurable_fst).mul
      ((measurable_C B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p.property).comp
        measurable_fst)).mul ((measurable_of_finite Paper.spinSign).comp measurable_snd)
  have hi3 : Integrable F3 P:=integrable_cavityZeroMarked_rest_centered_product μ n β ρ hβ hρ a p
    (cavityRestTerminalMeanPairing D μ p) G (measurable_cavityRestTerminalMeanPairing D μ p) hG
    3 1 (by norm_num) (norm_cavityRestTerminalMeanPairing_le_three D μ p)
    (fun z=>by
      rw [norm_mul,norm_mul,show ‖Paper.spinSign z.2‖=1 from by cases z.2 <;> norm_num [Paper.spinSign],mul_one]
      exact (mul_le_mul (scalar_M_norm_le_one B μ p z.1) (norm_C_le_one B μ p z.1)
        (norm_nonneg _) zero_le_one).trans_eq (one_mul (1:ℝ)))
  have hi4 : Integrable F4 P:=
    (cavityFixedRowMarked_kernel3_data_all_profiles μ n β ρ hβ hρ a p).1
  refine ⟨?_,?_⟩
  · change Integrable (fun z=>F0 z-2*Paper.parisiCDF μ p*F1 z-F2 z+2*F3 z-2*F4 z) P
    exact (((hi0.sub (hi1.const_mul (2*Paper.parisiCDF μ p))).sub hi2).add (hi3.const_mul 2)).sub (hi4.const_mul 2)
  · change (∫z,F0 z-2*Paper.parisiCDF μ p*F1 z-F2 z+2*F3 z-2*F4 z ∂P)=_
    rw [cavityLast_integral_combination P F0 F1 F2 F3 F4 _ hi0 hi1 hi2 hi3 hi4]
    have h0:(∫z,F0 z ∂P)=cavityRestCovarianceColumn D μ a p p*scalarResponseKernel0 B μ p p 0:=
      cavityZeroMarked_scalarSample_self_centered μ n β ρ hβ hρ a 0 p p 0
    have h1:(∫z,F1 z ∂P)=cavityRestCovarianceColumn D μ a p p*scalarResponseKernel1 B μ p p 0:=
      cavityZeroMarked_scalarSample_self_centered μ n β ρ hβ hρ a 1 p p 0
    have h2:=(cavityFixedRowMarked_strict_future_kernel2_data_all_profiles μ n β ρ hβ hρ a p).2
    have h3:(∫z,F3 z ∂P)=cavityRestCovarianceColumn D μ a p p*scalarResponseKernel1 B μ p p 0:=
      cavityZeroMarked_current_terminal_centered μ n β ρ hβ hρ a p
    have h4:=(cavityFixedRowMarked_kernel3_data_all_profiles μ n β ρ hβ hρ a p).2
    rw [h0,h1,h2,h3,h4]
    rw [cavitySignedResponseT1,cavitySignedResponse_original_T1_diagonal_zero,mul_zero,zero_sub]
    ring

end HexagonPaper
