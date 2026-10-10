module
public import HexagonPaper.CavityFixedRowExpansionRestFamilies

@[expose] public section

/-! Literal all-profile marked K3/K4 expectation contractions with their
actual signed residuals. The varying free level is interchanged with the
true marked law using joint bounded families, retaining profile atoms. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

theorem cavityFixedRowMarked_kernel3_integral_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,cavityRestTwoTimeMeanPairing D μ p r (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 3 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      ∫r,cavityRestCovarianceColumn D μ a p (min p r)*scalarResponseKernel3 B μ p r 0+
        cavitySignedScalarKernelOne B μ r p*(∫z,cavitySignedResponseSymmetricMeanResidual D μ p r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z ∂anisotropicMeasureSampleLaw D μ a)
        ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let B:=followupCavityScalarBeta n β ρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityRestTwoTimeMeanPairing D μ p z.1 z.2.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1
  have hm : Measurable F := by
    simpa only [Function.comp_def] using (measurable_cavityRestTwoTimeMeanPairing_centered_family D μ a p).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hb (z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)) : ‖F z‖≤6 := by
    dsimp only [F]
    exact norm_cavityRestTwoTimeMeanPairing_centered_family D μ a p p z.1 z.2
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id (fun _=>0) measurable_const measurable_id measurable_const F hm 6 (by norm_num) hb 3
  rw [←integral_integral_swap hi]
  apply integral_congr_ae
  exact .of_forall fun r=>cavityZeroMarked_kernel3_two_time_centered μ n β ρ hβ hρ a p r

theorem cavityFixedRowMarked_kernel4_integral_all_profiles
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (a : ℝ) (p : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,∫r,cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample 4 B μ p r 0 (cavityZeroMarkedSampleSplit n z).2 ∂parisiFreeMeasure μ a
      ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      ∫r,cavityRestCovarianceColumn D μ a p r*scalarResponseKernel4 B μ p r 0+
        cavitySignedScalarKernelMarked B (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ r p*
          (∫z,cavitySignedResponseTerminalResidual D μ r z*
            cavitySignedResponseCenteredSelfOverlap D μ a p z.1 ∂anisotropicMeasureSpinPathLaw D μ a)
        ∂parisiFreeMeasure μ a := by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  let F:=fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
    cavityRestTerminalMeanPairing D μ z.1 z.2*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (parisiFreeMeasure μ a)
    (fun _=>p) id (fun _=>0) measurable_const measurable_id measurable_const F
      (measurable_cavityRestTerminalMeanPairing_centered_family D μ a p) 6 (by norm_num)
      (fun z=>norm_cavityRestTerminalMeanPairing_centered_family D μ a p z.1 z.2) 4
  rw [←integral_integral_swap hi]
  apply integral_congr_ae
  exact .of_forall fun r=>cavityZeroMarked_kernel4_terminal_centered μ n β ρ hβ hρ a p r

end HexagonPaper
