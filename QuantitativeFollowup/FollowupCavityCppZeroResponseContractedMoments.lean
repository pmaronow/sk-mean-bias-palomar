module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseSeparatedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseScalarCoefficientAliases

@[expose] public section

/-! The actual terminal and two-time contractions split into the literal
scalar response kernel times the rest covariance column and the genuine
signed-response residual. Both terminal marks and all path coordinates
remain in the underlying independent joint law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
namespace QuantitativeFollowup
variable {n : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem contracted_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem cavityZeroMarked_kernel3_two_time_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p r : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityRestTwoTimeMeanPairing D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 3 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 contracted_zero_mem) μ a)=
      cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0+
        cavitySignedScalarKernelOne B μ r p*
        (∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a) :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F : AnisotropicDisorderBrownianSample n→ℝ:=fun z=>
    cavityRestTwoTimeMeanPairing D μ p r z*cavitySignedResponseCenteredSelfOverlap D μ a p z
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (p,z)) :=
    measurable_const.prodMk measurable_id
  have hC : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=by
    simpa only [Function.comp_def,Function.uncurry_def] using
      (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hm
  have hF : Measurable F :=
    (measurable_cavityRestTwoTimeMeanPairing D μ p r).mul
      hC
  have hMarked : Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityRestTwoTimeMeanPairing D μ p r z.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.1) :=
    ((measurable_cavityRestTwoTimeMeanPairing D μ p r).comp measurable_fst).mul
      (hC.comp measurable_fst)
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a
    (fun z=>cavityRestTwoTimeMeanPairing D μ p r z.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
    hMarked 3 p r 0,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavityRestTwoTimeMeanPairing D μ p r z*cavitySignedResponseCenteredSelfOverlap D μ a p z) hF,
    cavityRestTwoTimeMeanPairing_centered_integral,
    scalarResponseCoefficient3_eq_cavitySignedScalarKernelOne,
    scalarResponseKernel3_eq_cavitySignedScalarKernelOne]
  ring

theorem cavityZeroMarked_kernel4_terminal_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p r : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 4 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 contracted_zero_mem) μ a)=
      cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0+
        cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
        (∫z,cavitySignedResponseTerminalResidual D μ r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a) :=by
  dsimp only
  rw [cavityZeroMarked_scalarSample_terminal_centered μ n β ρ hβ hρ a 4 p r 0,
    scalarResponseCoefficient4_eq_cavitySignedScalarKernelMarked _
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne',
    scalarResponseKernel4_eq_cavitySignedScalarKernelMarked _
      (followupCavityScalarBeta_pos n β ρ hβ hρ).ne']
  ring

theorem cavityZeroMarked_kernel6_two_time_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (p r l : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityRestTwoTimeMeanPairing D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 6 B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 contracted_zero_mem) μ a)=
      cavityRestCovarianceColumn D μ a p (min r l)*scalarResponseKernel6 B μ p r l+
        cavitySignedScalarKernelTriple B μ (r,l) p*
        (∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a) :=by
  dsimp only
  rw [cavityZeroMarked_scalarSample_two_time_centered μ n β ρ hβ hρ a 6 p r l,
    scalarResponseCoefficient6_eq_cavitySignedScalarKernelTriple,
    scalarResponseKernel6_eq_cavitySignedScalarKernelTriple]
  ring

end QuantitativeFollowup
