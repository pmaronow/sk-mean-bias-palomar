module
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPreservingIntegrals
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalDefectTests
public import FourPapersCommon.ProbabilityIntegralContinuity

@[expose] public section

/-! The normalizer pattern uses the actual fresh conditional product law.
Its signed defect integral converges under preserving profiles, including
all endpoint atoms; the Gaussian/profile law and test continuity are genuine. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

def nativeStreamingFreshDefectMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) : ℝ :=
  ∫σ : Configuration (n+1) × Configuration (n+1),
    cavitySpinOverlapDefect n r σ.1 σ.2
      ∂(anisotropicBinarySpinProbability D μ a r :
        Measure (Configuration (n+1) × Configuration (n+1)))

theorem nativeStreamingFreshDefectMoment_eq_fresh (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    nativeStreamingFreshDefectMoment D μ a r =
      ∫z, cavitySpinOverlapDefect n r z.2.1 z.2.2
        ∂anisotropicFreshTerminalPairLaw D μ a r := by
  rw [nativeStreamingFreshDefectMoment, anisotropicBinarySpinProbability_eq_fresh_pair]
  exact integral_map_of_stronglyMeasurable measurable_snd
    (measurable_of_finite (fun σ : Configuration (n+1) × Configuration (n+1) =>
      cavitySpinOverlapDefect n r σ.1 σ.2)).stronglyMeasurable

theorem tendsto_nativeStreamingFreshDefectMoment
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated] (D : AnisotropicSpinModel (n+1))
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) {rj : L→Paper.Overlap} {r : Paper.Overlap} (hr : Tendsto rj l (𝓝 r)) :
    Tendsto (fun N => nativeStreamingFreshDefectMoment D (μj N) a (rj N)) l
      (𝓝 (nativeStreamingFreshDefectMoment D μ a r)) := by
  have hc : Continuous (fun z : Paper.Overlap × (Configuration (n+1) × Configuration (n+1)) =>
      cavitySpinOverlapDefect n z.1 z.2.1 z.2.2) :=
    continuous_prod_of_discrete_right.mpr (fun σ =>
      continuous_cavitySpinOverlapDefect_clock id continuous_id σ.1 σ.2)
  exact (continuous_integral_probability_of_joint _ hc).tendsto
      (r, anisotropicBinarySpinProbability D μ a r) |>.comp
    (hr.prodMk_nhds (tendsto_anisotropicBinarySpinProbability D hμ a hr))

theorem continuous_nativeStreamingFreshDefectMoment (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) : Continuous (nativeStreamingFreshDefectMoment D μ a) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  exact tendsto_nativeStreamingFreshDefectMoment D tendsto_const_nhds a tendsto_id

theorem nativeStreamingFreshDefectMoment_abs_le (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (a : ℝ) (r : Paper.Overlap) :
    |nativeStreamingFreshDefectMoment D μ a r| ≤ 2 := by
  simpa only [nativeStreamingFreshDefectMoment, Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const
      (μ := (anisotropicBinarySpinProbability D μ a r : Measure _))
      (f := fun σ : Configuration (n+1) × Configuration (n+1) =>
        cavitySpinOverlapDefect n r σ.1 σ.2) (C := (2 : ℝ))
      (.of_forall fun σ => by
        simpa only [Real.norm_eq_abs] using
          cavitySpinOverlapDefect_abs_le_two n r r.property σ.1 σ.2)

theorem tendsto_nativeStreamingNormalizerDefectIntegral (D : AnisotropicSpinModel (n+1))
    (μ : Paper.ParisiMeasure) (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a) :
    Tendsto (fun N => ∫r, nativeStreamingFreshDefectMoment D
      (FRSB.preservingMeasure μ S N) a r
        ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a) atTop
      (𝓝 (∫r, nativeStreamingFreshDefectMoment D μ a r ∂parisiFreeMeasure μ a)) :=
  nativeStreaming_free_integral_tendsto μ S hzero a ha hμ _ _
    (fun N => (continuous_nativeStreamingFreshDefectMoment D _ a).measurable) 2 (by norm_num)
    (fun N r => nativeStreamingFreshDefectMoment_abs_le D _ a r)
    (fun r => tendsto_nativeStreamingFreshDefectMoment D
      (FRSB.tendsto_preservingMeasure μ S) a (FRSB.tendsto_preservingRound S r))

end QuantitativeFollowup
