module
public import QuantitativeFollowup.FollowupCavityThirdMoment
public import QuantitativeFollowup.FollowupCavityParameters

@[expose] public section

/-! The actual physical third-moment family has a finite supremum; this
object is formed from the constructed laws, with no moment-bound premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}

theorem cavityThirdMoment_le_eight (D:AnisotropicSpinModel (n+1))
    (μ:Paper.ParisiMeasure) (a:ℝ) (ha:a∈Icc (0:ℝ) 1) :
    cavityThirdMoment D μ a≤8 := by
  have h:=integral_mono (integrable_cavityCubicPairMoment D μ a) (integrable_const (8:ℝ))
    (fun q=>(cavityCubicPairMoment_bounds D μ a q).2)
  rw [integral_const,Measure.real,parisiFreeMeasure_univ,
    ENNReal.toReal_ofReal (sub_nonneg.mpr ha.2)] at h
  exact h.trans (by simp only [smul_eq_mul];nlinarith[ha.1])

def cavityPhysicalCubicSupremum (n:ℕ) (μ:Paper.ParisiMeasure) (β ρ a:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) : ℝ :=
  sSup (Set.range (fun u:Paper.Overlap=>
    cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u u.property) μ a))

theorem cavityThirdMoment_le_physicalSupremum (μ:Paper.ParisiMeasure) (β ρ a:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (ha:a∈Icc (0:ℝ) 1)
    (u:ℝ) (hu:u∈Icc (0:ℝ) 1) :
    cavityThirdMoment (followupCavitySpinModel n β ρ hβ hρ u hu) μ a≤
      cavityPhysicalCubicSupremum n μ β ρ a hβ hρ := by
  apply le_csSup
  · exact ⟨8,by rintro _ ⟨v,rfl⟩;exact cavityThirdMoment_le_eight _ μ a ha⟩
  · exact ⟨⟨u,hu⟩,rfl⟩

theorem cavityPhysicalCubicSupremum_bounds (μ:Paper.ParisiMeasure) (β ρ a:ℝ)
    (hβ:0<β) (hρ:ρ∈Ioc (0:ℝ) 1) (ha:a∈Icc (0:ℝ) 1) :
    cavityPhysicalCubicSupremum n μ β ρ a hβ hρ∈Icc (0:ℝ) 8 := by
  constructor
  · exact (cavityThirdMoment_nonneg
      (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a).trans
      (cavityThirdMoment_le_physicalSupremum μ β ρ a hβ hρ ha 0 ⟨le_rfl,zero_le_one⟩)
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨u,rfl⟩
    exact cavityThirdMoment_le_eight _ μ a ha

end QuantitativeFollowup
