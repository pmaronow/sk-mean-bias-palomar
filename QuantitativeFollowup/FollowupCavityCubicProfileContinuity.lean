module
public import QuantitativeFollowup.FollowupCavityThirdMoment
public import QuantitativeFollowup.ParisiFreeIntegralContinuity

@[expose] public section

/-! Native cubic moments are jointly weakly continuous in profile and
split level. The integrated moment retains the prescribed root floor. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem continuous_cavityCubicPairMoment_profile (D : AnisotropicSpinModel (n+1)) (a : ℝ) :
    Continuous (fun z : Paper.ParisiMeasure × Paper.Overlap => cavityCubicPairMoment D z.1 a z.2) := by
  let f : (Paper.ParisiMeasure × Paper.Overlap) × (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z => |cavityRestOverlap n z.2.1 z.2.2-(z.1.2 : ℝ)|^3
  have hf : Continuous f := by
    have hc : Continuous (fun z : (Paper.ParisiMeasure × Paper.Overlap) ×
        (Configuration (n+1) × Configuration (n+1)) => cavityRestOverlap n z.2.1 z.2.2) :=
      (continuous_of_discreteTopology (f := Function.uncurry (cavityRestOverlap n))).comp continuous_snd
    exact (hc.sub (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).abs.pow 3
  have hp : Continuous (fun z : Paper.ParisiMeasure × Paper.Overlap =>
      anisotropicBinarySpinProbability D z.1 a z.2) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact tendsto_anisotropicBinarySpinProbability D continuous_fst.continuousAt a
      continuous_snd.continuousAt
  exact continuous_integral_probability_family f hf _ hp

theorem continuous_cavityThirdMoment_floor (D : AnisotropicSpinModel (n+1))
    (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) :
    Continuous (fun μ : ↥(scalarFloor a) => cavityThirdMoment D μ.val a) := by
  let g : ↥(scalarFloor a) × Paper.Overlap → Paper.ParisiMeasure × Paper.Overlap :=
    fun z => (z.1.val,z.2)
  have hg : Continuous g :=
    ((continuous_subtype_val : Continuous (Subtype.val : ↥(scalarFloor a) → Paper.ParisiMeasure)).comp
      (continuous_fst : Continuous (Prod.fst : ↥(scalarFloor a) × Paper.Overlap → ↥(scalarFloor a)))).prodMk
      (continuous_snd : Continuous (Prod.snd : ↥(scalarFloor a) × Paper.Overlap → Paper.Overlap))
  have hf : Continuous (fun z : ↥(scalarFloor a) × Paper.Overlap =>
      cavityCubicPairMoment D z.1.val a z.2) := by
    have hh := (continuous_cavityCubicPairMoment_profile D a).comp hg
    simpa only [g,Function.comp_def] using hh
  change Continuous (fun μ : ↥(scalarFloor a) => ∫q,cavityCubicPairMoment D μ.val a q
    ∂parisiFreeMeasure μ.val a)
  exact continuous_integral_parisiFreeMeasure_family a ha Subtype.val continuous_subtype_val
    (fun μ => μ.property) _ hf

theorem tendsto_cavityThirdMoment_of_weak (D : AnisotropicSpinModel (n+1))
    (ν : ℕ → Paper.ParisiMeasure) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a ∈ Icc (0 : ℝ) 1) (hνfloor : ∀j, ν j ∈ scalarFloor a)
    (hμfloor : μ ∈ scalarFloor a) (hν : Tendsto ν atTop (𝓝 μ)) :
    Tendsto (fun j => cavityThirdMoment D (ν j) a) atTop (𝓝 (cavityThirdMoment D μ a)) := by
  have ht : Tendsto (fun j => (⟨ν j,hνfloor j⟩ : ↥(scalarFloor a))) atTop
      (𝓝 (⟨μ,hμfloor⟩ : ↥(scalarFloor a))) := tendsto_subtype_rng.2 hν
  have hh := ((continuous_cavityThirdMoment_floor D a ha).tendsto
    (⟨μ,hμfloor⟩ : ↥(scalarFloor a))).comp ht
  simpa only [Function.comp_def] using hh

end QuantitativeFollowup
