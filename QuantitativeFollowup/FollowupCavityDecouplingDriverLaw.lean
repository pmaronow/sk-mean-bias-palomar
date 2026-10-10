module
public import QuantitativeFollowup.FollowupCavityDecouplingState

@[expose] public section

/-! The true zero-coupling sample map has the product law of the normalized
rest sample and an independent scalar Wiener sample. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

def cavityZeroSampleSplit (n : ℕ) (p : AnisotropicDisorderBrownianSample (n+1)) :
    AnisotropicDisorderBrownianSample n×Paper.BrownianSample:=
  (cavityRestSampleProjection n p,p.2 (Fin.last n))

theorem measurable_cavityZeroSampleSplit (n : ℕ) : Measurable (cavityZeroSampleSplit n) :=
  (((cavityRestDisorderProjection n).measurable.comp measurable_fst).prodMk
    (Measurable.of_eval fun i=>(measurable_pi_apply i.castSucc).comp measurable_snd)).prodMk
    ((measurable_pi_apply (Fin.last n)).comp measurable_snd)

theorem cavityZeroSampleSplit_law (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a).map
      (cavityZeroSampleSplit n)=
      (anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).prod
        Paper.canonicalBrownianMeasure := by
  let P:=anisotropicMeasureOuterLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a
  let R:=anisotropicMeasureOuterLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a
  have hsplit : cavityZeroSampleSplit n=MeasurableEquiv.prodAssoc.symm ∘
      Prod.map (cavityRestDisorderProjection n) (cavityWienerSplit n) := rfl
  unfold anisotropicMeasureSampleLaw
  rw [hsplit,←Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
      ((cavityRestDisorderProjection n).measurable.prodMap (measurable_cavityWienerSplit n)),
    ←Measure.map_prod_map _ _ (cavityRestDisorderProjection n).measurable (measurable_cavityWienerSplit n),
    followupCavityMeasureOuterLaw_zero,vectorBrownianMeasure_map_cavityWienerSplit]
  exact ((measurePreserving_prodAssoc R (vectorBrownianMeasure n) Paper.canonicalBrownianMeasure).symm
    MeasurableEquiv.prodAssoc).map_eq

theorem hasLaw_cavityZeroSampleSplit (μ : Paper.ParisiMeasure) (n : ℕ) (β ρ : ℝ) (hβ : 0<β)
    (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ) :
    HasLaw (cavityZeroSampleSplit n)
      ((anisotropicMeasureSampleLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a).prod
        Paper.canonicalBrownianMeasure)
      (anisotropicMeasureSampleLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,by norm_num⟩) μ a) :=
  ⟨(measurable_cavityZeroSampleSplit n).aemeasurable,cavityZeroSampleSplit_law μ n β ρ hβ hρ a⟩

end QuantitativeFollowup
