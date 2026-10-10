module
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments
public import QuantitativeFollowup.FollowupCavityCppZeroResponseRestMomentGrouping
public import QuantitativeFollowup.ScalarResponseSamples

@[expose] public section

/-! Exact contraction of the genuine independent endpoint law into the
literal scalar response coefficients and the actual rest covariance and
terminal/two-time residuals. The whole driving paths and terminal marks
remain present in each source integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper FRSB
open scoped BigOperators
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem separated_zero_mem : (0:ℝ)∈Icc 0 1:=⟨le_rfl,zero_le_one⟩

theorem integral_cavityZeroMarked_scalarResponseSample
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (F : AnisotropicDisorderBrownianSample n×Configuration n→ℝ) (hF : Measurable F)
    (j : Fin 8) (p r l : Paper.Overlap) :
    let B:=followupCavityScalarBeta n β ρ
    (∫z,F (cavityZeroMarkedSampleSplit n z).1*
      scalarResponseSample j B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 separated_zero_mem) μ a)=
      (∫z,F z ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
        scalarResponseCoefficient j B μ p r l :=by
  dsimp only
  rw [integral_cavityZeroMarked_product μ n β ρ hβ hρ a F _ hF
    (measurable_scalarResponseSample j _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ p r l),
    integral_scalarResponseSample]

private theorem measurable_rest_centered (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap) :
    Measurable (cavitySignedResponseCenteredSelfOverlap D μ a p) :=by
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (p,z)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def,Function.uncurry_def] using
    (measurable_joint_cavitySignedResponseCenteredSelfOverlap D μ a).comp hm

private theorem measurable_rest_self (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (r : Paper.Overlap) :
    Measurable (cavitySignedResponseSelfOverlap D μ r) :=by
  have hm : Measurable (fun z : AnisotropicDisorderBrownianSample n => (r,z)) :=
    measurable_const.prodMk measurable_id
  simpa only [Function.comp_def,Function.uncurry_def] using
    (measurable_joint_cavitySignedResponseSelfOverlap D μ).comp hm

theorem cavityZeroMarked_scalarSample_self_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (j : Fin 8) (p r l : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavitySignedResponseSelfOverlap D μ r (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample j B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 separated_zero_mem) μ a)=
      cavityRestCovarianceColumn D μ a p r*scalarResponseCoefficient j B μ p r l :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hF:Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavitySignedResponseSelfOverlap D μ r z.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.1):=
    ((measurable_rest_self D μ r).comp measurable_fst).mul
      ((measurable_rest_centered D μ a p).comp measurable_fst)
  have hX:Measurable (fun z : AnisotropicDisorderBrownianSample n=>
      cavitySignedResponseSelfOverlap D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z):=
    (measurable_rest_self D μ r).mul (measurable_rest_centered D μ a p)
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a _ hF,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavitySignedResponseSelfOverlap D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z) hX,
    ←cavityRestCovarianceColumn_eq_self_centered_moment]

theorem cavityZeroMarked_scalarSample_terminal_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (j : Fin 8) (p r l : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityRestTerminalMeanPairing D μ r (cavityZeroMarkedSampleSplit n z).1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample j B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 separated_zero_mem) μ a)=
      (cavityRestCovarianceColumn D μ a p r+
        ∫z,cavitySignedResponseTerminalResidual D μ r z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z.1
          ∂anisotropicMeasureSpinPathLaw D μ a)*scalarResponseCoefficient j B μ p r l :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hT:Measurable (cavityRestTerminalMeanPairing D μ r):=by
    unfold cavityRestTerminalMeanPairing
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i hi
    exact (((measurable_of_finite (fun τ : Configuration n=>Paper.spinSign (τ i))).comp
      measurable_snd).mul ((measurable_anisotropicProcessSpinResponse D μ r i).comp measurable_fst))
  have hF:Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityRestTerminalMeanPairing D μ r z*cavitySignedResponseCenteredSelfOverlap D μ a p z.1):=
    hT.mul ((measurable_rest_centered D μ a p).comp measurable_fst)
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a _ hF,
    cavityRestTerminalMeanPairing_centered_integral]

theorem cavityZeroMarked_scalarSample_two_time_centered
    (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (j : Fin 8) (p r l : Paper.Overlap) :
    let D:=followupCavityRestSpinModel n β ρ hβ hρ
    let B:=followupCavityScalarBeta n β ρ
    (∫z,cavityRestTwoTimeMeanPairing D μ r l (cavityZeroMarkedSampleSplit n z).1.1*
      cavitySignedResponseCenteredSelfOverlap D μ a p (cavityZeroMarkedSampleSplit n z).1.1*
      scalarResponseSample j B μ p r l (cavityZeroMarkedSampleSplit n z).2
      ∂anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 separated_zero_mem) μ a)=
      (cavityRestCovarianceColumn D μ a p (min r l)+
        ∫z,cavitySignedResponseSymmetricMeanResidual D μ r l z*
          cavitySignedResponseCenteredSelfOverlap D μ a p z
          ∂anisotropicMeasureSampleLaw D μ a)*scalarResponseCoefficient j B μ p r l :=by
  dsimp only
  let D:=followupCavityRestSpinModel n β ρ hβ hρ
  have hT:Measurable (cavityRestTwoTimeMeanPairing D μ r l):=by
    unfold cavityRestTwoTimeMeanPairing
    apply Measurable.div_const
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_anisotropicProcessSpinResponse D μ r i).mul
      (measurable_anisotropicProcessSpinResponse D μ l i)
  have hF:Measurable (fun z : AnisotropicDisorderBrownianSample n×Configuration n=>
      cavityRestTwoTimeMeanPairing D μ r l z.1*cavitySignedResponseCenteredSelfOverlap D μ a p z.1):=
    (hT.comp measurable_fst).mul ((measurable_rest_centered D μ a p).comp measurable_fst)
  have hX:Measurable (fun z : AnisotropicDisorderBrownianSample n=>
      cavityRestTwoTimeMeanPairing D μ r l z*cavitySignedResponseCenteredSelfOverlap D μ a p z):=
    hT.mul (measurable_rest_centered D μ a p)
  rw [integral_cavityZeroMarked_scalarResponseSample μ n β ρ hβ hρ a _ hF,
    integral_anisotropicMeasureSpinPathLaw_sample D μ a
      (fun z=>cavityRestTwoTimeMeanPairing D μ r l z*cavitySignedResponseCenteredSelfOverlap D μ a p z) hX,
    cavityRestTwoTimeMeanPairing_centered_integral]

end QuantitativeFollowup
