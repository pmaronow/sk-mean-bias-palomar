module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossPhysical
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossComponent
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw

@[expose] public section

/-! The computed raw cross component receives the genuine joint terminal
law of the two ORIGINAL locations. The observable may depend jointly on
every old terminal spin and on the ordered fresh spin pair. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem cavityGeneratedObservedRawCrossComponent_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m) (s t : CavityGeneratedRawCrossSite U.tree)
    (k : NativeStreamingGeneratedCrossEdgeChart) (h : CavityGeneratedHistory Paper.Overlap m)
    (r l : Paper.Overlap)
    (hr : cavityGeneratedRawCrossCell (U.clock h) U.tree s r)
    (hl : cavityGeneratedRawCrossCell (U.clock h) U.tree t l)
    (hk : cavityGeneratedRawCrossChartHolds U.tree s t k r l)
    (G : TerminalSpins (Configuration (n+1)) U.tree ×
      (Configuration (n+1)×Configuration (n+1))→ℝ) :
    (∫σ,G (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a
        (cavityGeneratedObservedRawCrossComponent U s t k) (cavityGeneratedRawCrossAppend h r l)) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginCrossProbability D μ a (U.clock h) U.tree
          (cavityGeneratedRawCrossOrigin U.tree s r) (cavityGeneratedRawCrossOrigin U.tree t l)) G := by
  unfold cavityGeneratedObservedRawComponentTerminalMeasure
  rw [cavityGeneratedObservedRawCrossComponent_clock_append U s t k h r l hr hl]
  change (∫ σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedRawCrossTree U.tree s t k),
    G (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ)
      ∂(anisotropicRecordedProfileTreeLaw D μ a
        (cavityGeneratedRawCrossObservationClock U.tree s t (U.clock h) r l)
        (cavityGeneratedRawCrossTree U.tree s t k)).map
          (fun z => finiteCascadeRecordTerminalSpins (cavityGeneratedRawCrossTree U.tree s t k) z.2)) = _
  refine Eq.trans (integral_map
    (μ := anisotropicRecordedProfileTreeLaw D μ a
      (cavityGeneratedRawCrossObservationClock U.tree s t (U.clock h) r l)
      (cavityGeneratedRawCrossTree U.tree s t k))
    ((measurable_finiteCascadeRecordTerminalSpins
      (cavityGeneratedRawCrossTree U.tree s t k)).comp measurable_snd).aemeasurable
    (measurable_of_finite (fun σ=>G (cavityGeneratedRawCrossTerminalProjection U.tree s t k σ))).aestronglyMeasurable) ?_
  exact cavityGeneratedRawCross_terminal_receiver D μ a U.tree s t k (U.clock h)
    (U.clock_antitone h) (U.clock_terminal h) r l hr hl hk G

end QuantitativeFollowup
