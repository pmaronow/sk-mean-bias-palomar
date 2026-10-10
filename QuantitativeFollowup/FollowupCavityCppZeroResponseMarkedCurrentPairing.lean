module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestMomentGrouping
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarCoefficientAliases

@[expose] public section

/-! The terminal-spin factor in the current last-coordinate response is
removed using the actual scalar conditional spin law. The rest terminal
pairing at the same level is conditioned by its genuine whole-past law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem currentPairing_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integral_cavityZeroMarked_mean_curvature_sign
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ) (hF : Measurable F)
    (p : Paper.Overlap) :
    let B:=followupCavityScalarBeta n β ρ
    (∫z,F (cavityZeroMarkedSampleSplit n z).1*
      (M B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        C B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        Paper.spinSign (cavityZeroMarkedSampleSplit n z).2.2)
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 currentPairing_zero_mem) μ a)=
      (∫z,F z ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
        scalarResponseCoefficient 1 B μ p p 0 :=by
  dsimp only
  have hM := (FRSB.measurable_M (followupCavityScalarBeta n β ρ) μ p p.property).comp
    (measurable_fst : Measurable (Prod.fst : Paper.BrownianSample×Bool→Paper.BrownianSample))
  have hC := (FRSB.measurable_C (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p.property).comp
    (measurable_fst : Measurable (Prod.fst : Paper.BrownianSample×Bool→Paper.BrownianSample))
  have hsign : Measurable (fun z : Paper.BrownianSample×Bool=>Paper.spinSign z.2) :=
    (measurable_of_finite Paper.spinSign).comp measurable_snd
  have hG:Measurable (fun z : Paper.BrownianSample×Bool=>
      M (followupCavityScalarBeta n β ρ) μ p z.1*
        C (followupCavityScalarBeta n β ρ) μ p z.1*Paper.spinSign z.2):=
    (hM.mul hC).mul hsign
  rw [integral_cavityZeroMarked_product μ n β ρ hβ hρ a F
      (fun z=>M (followupCavityScalarBeta n β ρ) μ p z.1*
        C (followupCavityScalarBeta n β ρ) μ p z.1*Paper.spinSign z.2) hF hG,
    integral_scalarMarkedSpinLaw_mean_curvature_sign_eq_coefficient1]

theorem cavityRestTerminalMeanPairing_current_centered_integral
    {n : ℕ} (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (p : Paper.Overlap) :
    (∫z,cavityRestTerminalMeanPairing D μ p z*
      cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)=
      cavityRestCovarianceColumn D μ a p p :=by
  rw [cavityRestTerminalMeanPairing_centered_integral,
    cavitySignedResponse_original_T1_diagonal_zero,add_zero]

theorem cavityZeroMarked_current_terminal_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,(cavityRestTerminalMeanPairing D μ p (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1)*
      (M B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        C B μ p (cavityZeroMarkedSampleSplit n z).2.1*
        Paper.spinSign (cavityZeroMarkedSampleSplit n z).2.2)
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 currentPairing_zero_mem) μ a)=
      cavityRestCovarianceColumn D μ a p p*scalarResponseKernel1 B μ p p 0 :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (p,z)) :=
    measurable_const.prodMk measurable_id
  have hC : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=by
    simpa only [Function.comp_def,Function.uncurry_def] using
      (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hm
  have hF : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityRestTerminalMeanPairing D μ p z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1) :=
    (measurable_cavityRestTerminalMeanPairing D μ p).mul
      (hC.comp measurable_fst)
  rw [integral_cavityZeroMarked_mean_curvature_sign μ n β ρ hβ hρ a _ hF p,
    cavityRestTerminalMeanPairing_current_centered_integral]
  rfl

end QuantitativeFollowup
