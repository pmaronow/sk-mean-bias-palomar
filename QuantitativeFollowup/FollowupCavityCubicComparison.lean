module
public import QuantitativeFollowup.FollowupCavityNativeComparison
public import QuantitativeFollowup.FollowupCavityThirdMoment

@[expose] public section

/-! Uniform interpolation comparison of the genuine native two-fresh
cubic moment and its integral against the actual free profile measure. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityBinaryObservation_energy_integral (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (p : Paper.Overlap)
    (F : Configuration n × Configuration n → ℝ) :
    (∫z : CavityPathRecordSpace anisotropicBinaryObservationTree n,
      F (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2)
      ∂(anisotropicRecordedEnergyProbability D μ a (anisotropicBinaryObservationSchedule p)
        anisotropicBinaryObservationTree : Measure (CavityPathRecordSpace anisotropicBinaryObservationTree n))) =
      ∫σ, F σ ∂(anisotropicBinarySpinProbability D μ a p : Measure _) := by
  let Ft : TerminalSpins (Configuration n) anisotropicBinaryObservationTree → ℝ := F
  have hF : Measurable Ft := measurable_of_finite Ft
  change (∫z : CavityPathRecordSpace anisotropicBinaryObservationTree n,
      Ft (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2) ∂_) = _
  rw [anisotropicRecordedEnergyProbability_measure,integral_map
    (f := fun z : CavityPathRecordSpace anisotropicBinaryObservationTree n =>
      Ft (finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree z.2))
    ((measurable_anisotropicObservationEnergy D).prodMap
      (measurable_observationTreeMap _ (measurable_anisotropicObservationEnergy D) anisotropicBinaryObservationTree)).aemeasurable
    (hF.comp ((measurable_finiteCascadeRecordTerminalSpins anisotropicBinaryObservationTree).comp measurable_snd)).aestronglyMeasurable]
  change (∫z, F (anisotropicBinaryObservationSpins z.2)
    ∂anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      anisotropicBinaryObservationTree) = _
  change _ = ∫σ,F σ ∂(anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
    anisotropicBinaryObservationTree).map (anisotropicBinaryObservationSpins ∘ Prod.snd)
  exact (integral_map (μ := anisotropicRecordedProfileTreeLaw D μ a (anisotropicBinaryObservationSchedule p)
      anisotropicBinaryObservationTree)
    (measurable_anisotropicBinaryObservationSpins.comp measurable_snd).aemeasurable
    (measurable_of_finite F).aestronglyMeasurable).symm

theorem cavityCubicPairMoment_comparison
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0) (p : Paper.Overlap)
    (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a p ≤
      Real.exp (21*β^2)*cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a p := by
  have hq : Antitone (anisotropicBinaryObservationSchedule p) := by
    apply antitone_nat_of_succ_le
    intro j
    cases j with
    | zero => exact p.property.2
    | succ j => cases j with
      | zero => exact p.property.1
      | succ j => exact le_refl _
  let F : Configuration (n+1) × Configuration (n+1) → ℝ :=
    fun σ => |cavityRestOverlap n σ.1 σ.2-(p : ℝ)|^3
  have hh := cavityNative_positive_spin_comparison hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) hq 2 (by norm_num) rfl rfl
    anisotropicBinaryObservationTree F (fun _ => by positivity) u v hu hv
  rw [cavityBinaryObservation_energy_integral,cavityBinaryObservation_energy_integral] at hh
  change cavityCubicPairMoment _ μ a p ≤ _*cavityCubicPairMoment _ μ a p at hh
  convert hh using 1 <;> norm_num [anisotropicBinaryObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount] <;> ring <;> simp

theorem cavityThirdMoment_comparison
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (u v : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a ≤
      Real.exp (21*β^2)*cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ v hv) μ a := by
  rw [cavityThirdMoment,cavityThirdMoment,←integral_const_mul]
  exact integral_mono (integrable_cavityCubicPairMoment _ μ a)
    ((integrable_cavityCubicPairMoment _ μ a).const_mul _)
    (fun p => cavityCubicPairMoment_comparison hn β ρ hβ hρ μ a ha hfloor p u v hu hv)

end QuantitativeFollowup
