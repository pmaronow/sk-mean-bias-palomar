module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingNormalizerDefectIntegral
public import QuantitativeFollowup.AnisotropicRecordedProfileLawConvergence

@[expose] public section

/-! The original terminal expectation and the independent normalizer
pattern converge under genuine weak profiles. Bounded continuous tests
are built from the finite terminal-spin space inside the proof. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem tendsto_nativeStreamingOldTerminalExpectation
    {L : Type*} {l : Filter L} [l.IsCountablyGenerated]
    (D : AnisotropicSpinModel (n+1))
    {μj : L→Paper.ParisiMeasure} {μ : Paper.ParisiMeasure} (hμ : Tendsto μj l (𝓝 μ))
    (a : ℝ) (q : ℕ→Paper.Overlap) (hq : Antitone q)
    (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) :
    Tendsto (fun N => nativeStreamingOldTerminalExpectation D (μj N) a q T F) l
      (𝓝 (nativeStreamingOldTerminalExpectation D μ a q T F)) := by
  classical
  let C : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, ‖F σ‖
  have hb (σ : TerminalSpins (Configuration (n+1)) T) : ‖F σ‖≤C :=
    Finset.single_le_sum (fun σ _ => norm_nonneg (F σ)) (Finset.mem_univ σ)
  let f : (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T)→ᵇℝ :=
    BoundedContinuousFunction.mkOfBound
      ⟨fun z => F (finiteCascadeRecordTerminalSpins T z.2),
        (continuous_of_discreteTopology (f := F)).comp
          ((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_snd)⟩
      (2*C) (fun z w => (dist_le_norm_add_norm _ _).trans
        ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
  have hp := tendsto_anisotropicRecordedProfileProbability D hμ a q T
    (fun j _ => hq (Nat.le_succ j))
  have hi := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hp f
  change Tendsto (fun N => ∫z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T,
    F (finiteCascadeRecordTerminalSpins T z.2)
    ∂(anisotropicRecordedProfileProbability D (μj N) a q T :
      Measure (AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T))) l
    (𝓝 (∫z : AnisotropicObservationState (n+1) ×
        Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T,
      F (finiteCascadeRecordTerminalSpins T z.2)
      ∂(anisotropicRecordedProfileProbability D μ a q T :
        Measure (AnisotropicObservationState (n+1) ×
          Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T)))) at hi
  simpa only [nativeStreamingOldTerminalExpectation, anisotropicRecordedProfileProbability,
    Measure.coe_toProbabilityMeasure] using hi

theorem tendsto_nativeStreamingNormalizerPatternIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (S : Finset Paper.Overlap) (hzero : zeroOverlap∈S) :
    Tendsto (fun N => a * nativeStreamingOldTerminalExpectation D
      (FRSB.preservingMeasure μ S N) a q T F *
      (∫r, ∫z, cavitySpinOverlapDefect n r z.2.1 z.2.2
        ∂anisotropicFreshTerminalPairLaw D (FRSB.preservingMeasure μ S N) a r
          ∂parisiFreeMeasure (FRSB.preservingMeasure μ S N) a)) atTop
      (𝓝 (a * nativeStreamingOldTerminalExpectation D μ a q T F *
        (∫r, ∫z, cavitySpinOverlapDefect n r z.2.1 z.2.2
          ∂anisotropicFreshTerminalPairLaw D μ a r ∂parisiFreeMeasure μ a))) := by
  simpa only [nativeStreamingFreshDefectMoment_eq_fresh] using
    ((tendsto_nativeStreamingOldTerminalExpectation D (FRSB.tendsto_preservingMeasure μ S)
      a q hq T F).const_mul a).mul
      (tendsto_nativeStreamingNormalizerDefectIntegral D μ S hzero a ha hμ)

end QuantitativeFollowup
