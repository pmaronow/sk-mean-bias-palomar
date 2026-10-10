module
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw
public import QuantitativeFollowup.FollowupCavityThreeDefectAlgebra
public import FourPapersCommon.ProbabilityIntegralContinuity

@[expose] public section

/-! The literal cavity third moment uses the actual two-fresh conditional
terminal-spin law. Its level integral is a genuine finite free-measure
integral, including endpoint atoms and repeated split levels. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 500000
variable {n : ℕ}

def cavityCubicPairMoment (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (q : Paper.Overlap) : ℝ :=
  ∫ z : Configuration (n+1) × Configuration (n+1), |cavityRestOverlap n z.1 z.2-(q:ℝ)|^3
    ∂(anisotropicBinarySpinProbability D μ a q : Measure _)

theorem continuous_cavityCubicPairMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) : Continuous (cavityCubicPairMoment D μ a) := by
  let f : Paper.Overlap × (Configuration (n+1) × Configuration (n+1)) → ℝ :=
    fun z => |cavityRestOverlap n z.2.1 z.2.2-(z.1:ℝ)|^3
  have hf : Continuous f := by
    have hc : Continuous (fun z : Paper.Overlap × (Configuration (n+1) × Configuration (n+1)) =>
        cavityRestOverlap n z.2.1 z.2.2) :=
      (continuous_of_discreteTopology (f:=Function.uncurry (cavityRestOverlap n))).comp continuous_snd
    exact (hc.sub (continuous_subtype_val.comp continuous_fst)).abs.pow 3
  exact continuous_integral_probability_family f hf _
    (continuous_anisotropicBinarySpinProbability_split D μ a)

theorem cavityCubicPairMoment_bounds (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    cavityCubicPairMoment D μ a q ∈ Icc (0:ℝ) 8 := by
  constructor
  · exact integral_nonneg (fun _ => by positivity)
  · have hb (z : Configuration (n+1) × Configuration (n+1)) :
        |cavityRestOverlap n z.1 z.2-(q:ℝ)|^3 ≤ 8 := by
      have ha : |cavityRestOverlap n z.1 z.2-(q:ℝ)| ≤ 2 := by
        apply (abs_sub _ _).trans
        rw [abs_of_nonneg q.property.1]
        linarith [cavityRestOverlap_abs_le_one n z.1 z.2,q.property.2]
      have hh := pow_le_pow_left₀ (abs_nonneg (cavityRestOverlap n z.1 z.2-(q:ℝ))) ha 3
      norm_num at hh
      exact hh
    have hi : Integrable (fun z : Configuration (n+1) × Configuration (n+1) =>
        |cavityRestOverlap n z.1 z.2-(q:ℝ)|^3)
        (anisotropicBinarySpinProbability D μ a q : Measure _) := by
      exact (integrable_const (8:ℝ)).mono'
        (measurable_of_finite _).aestronglyMeasurable
        (.of_forall (fun z => by rw [Real.norm_of_nonneg (by positivity)]; exact hb z))
    exact (integral_mono hi (integrable_const (8:ℝ)) hb).trans_eq (by simp)

theorem cavityCubicPairMoment_eq_fresh (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : Paper.Overlap) :
    cavityCubicPairMoment D μ a q =
      ∫ z : Configuration (n+1) × Configuration (n+1), |cavityRestOverlap n z.1 z.2-(q:ℝ)|^3
        ∂(anisotropicFreshTerminalPairLaw D μ a q).snd := by
  rw [cavityCubicPairMoment,anisotropicBinarySpinProbability_eq_fresh_pair]

def cavityThirdMoment (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) : ℝ :=
  ∫ q, cavityCubicPairMoment D μ a q ∂parisiFreeMeasure μ a

theorem integrable_cavityCubicPairMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) :
    Integrable (cavityCubicPairMoment D μ a) (parisiFreeMeasure μ a) := by
  simpa only [IntegrableOn,Measure.restrict_univ] using
    (continuous_cavityCubicPairMoment D μ a).continuousOn.integrableOn_compact
      (μ:=parisiFreeMeasure μ a) isCompact_univ

theorem cavityThirdMoment_nonneg (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) : 0≤cavityThirdMoment D μ a :=
  integral_nonneg (fun q => (cavityCubicPairMoment_bounds D μ a q).1)

end QuantitativeFollowup
