module
public import QuantitativeFollowup.FollowupCavityDecouplingSpinMoments
public import QuantitativeFollowup.ThreeDescendantResponseMoments

@[expose] public section

/-! Native old-spin pair moments and conditional covariance entries at zero
incident coupling. They follow from genuine finite posterior transport. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

 theorem cavityRestProcessParameter_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample (n+1)) :
    cavityRestParameterProjection n (anisotropicProcessParameter
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q ω)=
      anisotropicProcessParameter (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (cavityRestSampleProjection n ω) := by
  unfold anisotropicProcessParameter
  rw [anisotropicDisorderInjection_apply,←anisotropicParameterPoint_field,
    cavityRestParameterProjection_point,cavityRestMeasureState_zero μ n β ρ hβ hρ q q.property ω,
    anisotropicParameterPoint_field]
  rfl

 theorem cavityRestOrderedCoupling_castSucc {n : ℕ} (i j : Fin n) :
    cavityRestCouplingEmbedding n (anisotropicOrderedCoupling i j)=
      anisotropicOrderedCoupling i.castSucc j.castSucc := by
  apply Subtype.ext
  by_cases hij : i≤j
  · have hc : i.castSucc ≤ j.castSucc := hij
    simp [anisotropicOrderedCoupling,min_eq_left hij,max_eq_right hij,
      min_eq_left hc,max_eq_right hc,cavityRestCouplingEmbedding]
  · have hji : j ≤ i := le_of_not_ge hij
    have hc : j.castSucc ≤ i.castSucc := hji
    simp [anisotropicOrderedCoupling,min_eq_right hji,max_eq_left hji,
      min_eq_right hc,max_eq_left hc,cavityRestCouplingEmbedding]

 theorem cavityRestProcessPairResponse_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample (n+1)) (i j : Fin n) :
    anisotropicProcessPairResponse
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q
        (anisotropicOrderedCoupling i.castSucc j.castSucc) ω=
      anisotropicProcessPairResponse (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (anisotropicOrderedCoupling i j) (cavityRestSampleProjection n ω) := by
  unfold anisotropicProcessPairResponse
  rw [←cavityRestOrderedCoupling_castSucc,cavityRestTailPairResponse_zero,cavityRestProcessParameter_zero]

 theorem cavityRestProcessSpinCovariance_zero (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (q : Paper.Overlap)
    (ω : AnisotropicDisorderBrownianSample (n+1)) (i j : Fin n) :
    anisotropicProcessSpinCovariance
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ q ω i.castSucc j.castSucc=
      anisotropicProcessSpinCovariance (followupCavityRestSpinModel n β ρ hβ hρ) μ q
        (cavityRestSampleProjection n ω) i j := by
  change anisotropicProcessPairResponse _ μ q (anisotropicOrderedCoupling i.castSucc j.castSucc) ω-
    anisotropicProcessMagnetization _ μ q ω i.castSucc*anisotropicProcessMagnetization _ μ q ω j.castSucc=_
  rw [cavityRestProcessPairResponse_zero]
  have hi:=congrArg (fun x : QuantitativePaper.Field n=>x i)
    (cavityRestProcessMagnetization_zero μ n β ρ hβ hρ q ω)
  have hj:=congrArg (fun x : QuantitativePaper.Field n=>x j)
    (cavityRestProcessMagnetization_zero μ n β ρ hβ hρ q ω)
  simp only [cavityRestFieldProjection_apply] at hi hj
  rw [hi,hj]
  rfl

 theorem hasLaw_cavityRestSampleProjection (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    HasLaw (cavityRestSampleProjection n)
      (anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)
      (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a) := by
  have hfst : HasLaw Prod.fst
      (anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)
      ((anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).prod
        Paper.canonicalBrownianMeasure) :=
    ⟨measurable_fst.aemeasurable,measurePreserving_fst.map_eq⟩
  exact hfst.comp (hasLaw_cavityZeroSampleSplit μ n β ρ hβ hρ a)

end QuantitativeFollowup
