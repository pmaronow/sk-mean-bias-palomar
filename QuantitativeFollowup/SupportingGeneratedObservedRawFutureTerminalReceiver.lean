module
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureComponent
public import QuantitativeFollowup.SupportingGeneratedObservedRawFutureLaw
public import QuantitativeFollowup.SupportingGeneratedObservedRawComponentLaw

@[expose] public section

/-! On its actual source cell the computed raw component has the true
original selected-origin future terminal law. An arbitrary old terminal
test is retained before multiplication by the new overlap defect. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem cavityGeneratedObservedRawFutureComponent_clock_on_event
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (hH : H ∈ cavityGeneratedObservedRawFutureComponentEvent U γ j) :
    (cavityGeneratedObservedRawFutureComponent U γ j).clock H =
      cavityGeneratedObservedRawFutureComponentClock U γ j H := by
  have hmono := cavityGeneratedObservedRawFutureClock_antitone
    (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) (U.clock_antitone _)
    U.tree γ j (H cavityGeneratedObservedRawFutureFirstMark)
      (H cavityGeneratedObservedRawFutureSecondMark) hH.2
  unfold CavityGeneratedObservedRawComponent.clock
  rw [cavityGeneratedObservedRawFutureComponent_rawClock]
  funext k
  exact cavityGeneratedClippedClock_eq _ k (fun i _ => hmono (Nat.le_succ i)) k le_rfl

theorem cavityGeneratedObservedRawFutureComponent_terminal_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedObservedRawComponent m)
    (γ : CavityGeneratedObservedRawOriginChart U.tree) (j : Fin U.depth)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (hH : H ∈ cavityGeneratedObservedRawFutureComponentEvent U γ j)
    (G : TerminalSpins (Configuration (n+1)) U.tree ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    (∫σ, G (cavityGeneratedObservedRawFutureTerminalProject U.tree γ j σ)
      ∂cavityGeneratedObservedRawComponentTerminalMeasure D μ a
        (cavityGeneratedObservedRawFutureComponent U γ j) H) =
      nativeStreamingTerminalMarkMoment
        (nativeStreamingOriginFutureProbability D μ a
          (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) U.tree
          (cavityGeneratedObservedRawFutureOrigin U.tree γ (H cavityGeneratedObservedRawFutureFirstMark))
          j (H cavityGeneratedObservedRawFutureSecondMark)) G := by
  let ψ := fun z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        (finiteCascadeFutureVertexGraft (cavityGeneratedObservedRawFutureAnchor U.tree γ j)
          (cavityGeneratedObservedRawFutureSplit U.tree γ j)) =>
      finiteCascadeRecordTerminalSpins _ z.2
  have hψ : Measurable ψ := (measurable_finiteCascadeRecordTerminalSpins _).comp measurable_snd
  have hG : Measurable (fun σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeFutureVertexGraft (cavityGeneratedObservedRawFutureAnchor U.tree γ j)
        (cavityGeneratedObservedRawFutureSplit U.tree γ j)) =>
      G (cavityGeneratedObservedRawFutureTerminalProject U.tree γ j σ)) := measurable_of_finite _
  unfold cavityGeneratedObservedRawComponentTerminalMeasure
  change (∫σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeFutureVertexGraft (cavityGeneratedObservedRawFutureAnchor U.tree γ j)
        (cavityGeneratedObservedRawFutureSplit U.tree γ j)),
    G (cavityGeneratedObservedRawFutureTerminalProject U.tree γ j σ)
      ∂(anisotropicRecordedProfileTreeLaw D μ a
        ((cavityGeneratedObservedRawFutureComponent U γ j).clock H)
        (finiteCascadeFutureVertexGraft (cavityGeneratedObservedRawFutureAnchor U.tree γ j)
          (cavityGeneratedObservedRawFutureSplit U.tree γ j))).map ψ) = _
  rw [integral_map hψ.aemeasurable hG.aestronglyMeasurable,
    cavityGeneratedObservedRawFutureComponent_clock_on_event U γ j H hH]
  let f := fun z : (AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) U.tree) ×
        (Configuration (n+1) × Configuration (n+1)) =>
      G (finiteCascadeRecordTerminalSpins U.tree z.1.2,z.2)
  have hf : Measurable f := (measurable_of_finite G).comp
    (((measurable_finiteCascadeRecordTerminalSpins U.tree).comp measurable_fst.snd).prodMk measurable_snd)
  unfold nativeStreamingTerminalMarkMoment
  rw [←cavityGeneratedObservedRawFuture_record_law D μ a
    (U.clock (cavityGeneratedObservedRawFutureHistoryPrefix H)) U.tree γ j
    (H cavityGeneratedObservedRawFutureFirstMark) (H cavityGeneratedObservedRawFutureSecondMark) hH.2.2.2.2,
    integral_map (measurable_cavityGeneratedObservedRawFutureRecordProject U.tree γ j).aemeasurable
      hf.aestronglyMeasurable]
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G (cavityGeneratedObservedRawFutureTerminalProject_record U.tree γ j z)

end QuantitativeFollowup
