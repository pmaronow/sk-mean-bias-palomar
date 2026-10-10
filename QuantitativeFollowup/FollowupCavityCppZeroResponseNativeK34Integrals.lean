module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseContractedMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseMarkedSampleIntegrability
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeFubini
public import QuantitativeFollowup.FollowupCavityCppZeroResponseFiniteFreeLinearity

@[expose] public section

/-! Exact free-measure contractions of the two-time K3 and terminal K4
terms. Their native centered residuals remain literal, rather than being
discarded in a conditional-moment approximation. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
variable {k : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem kernel34_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integral_cavityZeroMarked_free_kernel3
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,cavityRestTwoTimeMeanPairing D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 3 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 kernel34_zero_mem) μ a)=
      (∫r,cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      ∫r,cavitySignedScalarKernelOne B μ r p*
        (∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z
          ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 kernel34_zero_mem) μ a
  let F:=fun z r=>cavityRestTwoTimeMeanPairing D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
    cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
    scalarResponseSample 3 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
  have hi (r : Paper.Overlap) : Integrable (fun z=>F z r) P :=by
    have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
      (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
        ((anisotropicBrownianFiltration n).le _) le_rfl
    exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
      (fun z=>cavityRestTwoTimeMeanPairing D μ p r z.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
      (((measurable_cavityRestTwoTimeMeanPairing D μ p r).mul hcenter).comp measurable_fst)
      6 (by norm_num) (fun z=>by
        rw [norm_mul]
        exact (mul_le_mul (norm_cavityRestTwoTimeMeanPairing_le_three D μ p r z.1)
          (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
          (norm_nonneg _) (by norm_num : 0≤(3:ℝ))).trans_eq (by norm_num)) 3 p r 0
  change (∫z,∫r,F z r ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_swap P s a ha has hq F hi]
  calc
    _ = ∫r,cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0+
        cavitySignedScalarKernelOne B μ r p*
          (∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
            cavitySignedResponseCenteredSelfOverlap D μ a p z
            ∂anisotropicMeasureSampleLaw D μ a) ∂parisiFreeMeasure μ a :=by
      apply integral_congr_ae
      exact .of_forall fun r=>cavityZeroMarked_kernel3_two_time_centered μ n β ρ hβ hρ a p r
    _ = _ := integral_cavityFiniteFree_add s a ha has hq _ _

theorem integral_cavityZeroMarked_free_kernel4
    (s : RSBScheme k) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) (ha : 0≤a)
    (has : a ≤ s.m 1) (hq : s.q 1=0) (p : Paper.Overlap) :
    let μ:=Paper.parisiSchemeMeasure s
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 4 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
      ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 kernel34_zero_mem) μ a)=
      (∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0
        ∂parisiFreeMeasure μ a)+
      ∫r,cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
        (∫z,cavitySignedResponseTerminalResidual D μ r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a :=by
  dsimp only
  let μ:=Paper.parisiSchemeMeasure s
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let P:=anisotropicMeasureSpinPathLaw
    (followupCavitySpinModel n β ρ hβ hρ 0 kernel34_zero_mem) μ a
  let F:=fun z r=>cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
    cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
    scalarResponseSample 4 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2
  have hi (r : Paper.Overlap) : Integrable (fun z=>F z r) P :=by
    have hcenter : Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=
      (adapted_cavitySignedResponseCenteredSelfOverlap D μ a p).mono
        ((anisotropicBrownianFiltration n).le _) le_rfl
    exact integrable_cavityZeroMarked_scalarResponseSample_product μ n β ρ hβ hρ a
      (fun z=>cavityRestTerminalMeanPairing D μ r z*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.1)
      ((measurable_cavityRestTerminalMeanPairing D μ r).mul (hcenter.comp measurable_fst))
      6 (by norm_num) (fun z=>by
        rw [norm_mul]
        exact (mul_le_mul (norm_cavityRestTerminalMeanPairing_le_three D μ r z)
          (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
          (norm_nonneg _) (by norm_num : 0≤(3:ℝ))).trans_eq (by norm_num)) 4 p r 0
  change (∫z,∫r,F z r ∂parisiFreeMeasure μ a ∂P)=_
  rw [integral_cavityFiniteFree_swap P s a ha has hq F hi]
  calc
    _ = ∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0+
        cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
          (∫z,cavitySignedResponseTerminalResidual D μ r z*
            cavitySignedResponseCenteredSelfOverlap D μ a p z.1
            ∂anisotropicMeasureSpinPathLaw D μ a) ∂parisiFreeMeasure μ a :=by
      apply integral_congr_ae
      exact .of_forall fun r=>cavityZeroMarked_kernel4_terminal_centered μ n β ρ hβ hρ a p r
    _ = _ := integral_cavityFiniteFree_add s a ha has hq _ _

end QuantitativeFollowup
