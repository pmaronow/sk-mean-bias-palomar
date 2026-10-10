module
public import HexagonPaper.CavityFixedRowExpansionMarkedFubini
public import QuantitativeFollowup.AnisotropicSpinSecondRegularity
public import QuantitativeFollowup.FollowupCavityCppZeroResponseContractedMoments

@[expose] public section

/-! Joint measurable bounded rest pairings for the literal all-profile
marked contractions. Both varying time arguments are retained. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {n : ℕ}

theorem measurable_cavityRestTwoTimeMeanPairing_levels (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×AnisotropicDisorderBrownianSample n=>
      cavityRestTwoTimeMeanPairing D μ z.1.1 z.1.2 z.2) := by
  unfold cavityRestTwoTimeMeanPairing
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  simpa only [Function.comp_def,Pi.mul_def] using ((measurable_uncurry_anisotropicProcessSpinResponse D μ i).comp
    (measurable_fst.fst.prodMk measurable_snd)).mul
      ((measurable_uncurry_anisotropicProcessSpinResponse D μ i).comp
        (measurable_fst.snd.prodMk measurable_snd))

theorem measurable_cavityRestTerminalMeanPairing_level (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) :
    Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestTerminalMeanPairing D μ z.1 z.2) := by
  unfold cavityRestTerminalMeanPairing
  apply Measurable.div_const
  apply Finset.measurable_sum
  intro i _
  simpa only [Function.comp_def,Pi.mul_def] using ((measurable_of_finite (fun τ : Configuration n=>Paper.spinSign (τ i))).comp
    measurable_snd.snd).mul ((measurable_uncurry_anisotropicProcessSpinResponse D μ i).comp
      (measurable_fst.prodMk measurable_snd.fst))

theorem measurable_cavityRestTwoTimeMeanPairing_centered_family (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestTwoTimeMeanPairing D μ z.1.1 z.1.2 z.2.1*
        cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) :=
by
  have h1 : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestTwoTimeMeanPairing D μ z.1.1 z.1.2 z.2.1) := by
    simpa only [Function.comp_def] using (measurable_cavityRestTwoTimeMeanPairing_levels D μ).comp
      (measurable_fst.prodMk measurable_snd.fst)
  have h2 : Measurable (fun z : (Paper.Overlap×Paper.Overlap)×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
        (measurable_const.prodMk measurable_snd.fst))
  exact h1.mul h2

theorem norm_cavityRestTwoTimeMeanPairing_centered_family (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r l : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavityRestTwoTimeMeanPairing D μ r l z.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.1‖≤6 := by
  rw [norm_mul]
  exact (mul_le_mul (norm_cavityRestTwoTimeMeanPairing_le_three D μ r l z.1)
    (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
    (norm_nonneg _) (by norm_num : 0≤(3:ℝ))).trans_eq (by norm_num)

theorem measurable_cavityRestTerminalMeanPairing_centered_family (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavityRestTerminalMeanPairing D μ z.1 z.2*cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) :=
by
  have h2 : Measurable (fun z : Paper.Overlap×(AnisotropicDisorderBrownianSample n×Configuration n)=>
      cavitySignedResponseCenteredSelfOverlap D μ a p z.2.1) := by
    simpa only [Function.comp_def,Function.uncurry_def] using
      ((measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp
        (measurable_const.prodMk measurable_snd.fst))
  exact (measurable_cavityRestTerminalMeanPairing_level D μ).mul h2

theorem norm_cavityRestTerminalMeanPairing_centered_family (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p r : Paper.Overlap)
    (z : AnisotropicDisorderBrownianSample n×Configuration n) :
    ‖cavityRestTerminalMeanPairing D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1‖≤6 := by
  rw [norm_mul]
  exact (mul_le_mul (norm_cavityRestTerminalMeanPairing_le_three D μ r z)
    (norm_cavitySignedResponseCenteredSelfOverlap_le D μ a p z.1)
    (norm_nonneg _) (by norm_num : 0≤(3:ℝ))).trans_eq (by norm_num)

end HexagonPaper
