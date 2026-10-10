module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPairObservedMarkov

@[expose] public section

/-! Discarding a genuine inserted edge state recovers the entire original
record. The exact one-slot selection and native refinement laws already
use the transition semigroup, including repeated and endpoint clocks. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n J : ℕ}

theorem nativeStreamingEdgeObservedKernel_snd
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    (nativeStreamingEdgeObservedKernel D μ q T e r).map Prod.snd =
      anisotropicRecordedProfileTreeKernel D μ q T := by
  let d := nativeStreamingEdgeSubdivision e.depth
  let Q := nativeStreamingEdgeSchedule q e.depth r
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q hq e.depth r hr
  have hlevels : ∀j,Q (observationRefinementDepth d j)=q j :=
    nativeStreamingEdgeSchedule_refinement q e.depth r
  have hp : 0<d e.depth := by simp [d,nativeStreamingEdgeSubdivision]
  have hmark : Q (observationRefinementDepth d e.depth+0+1)=r := by
    simp [Q,d,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  have hk := nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e 0 hp
  rw [hmark] at hk
  have hm := measurable_nativeStreamingEdgeSelection
    (E:=AnisotropicObservationState n) (S:=Configuration n) d e 0
  have he : Prod.snd ∘ nativeStreamingEdgeSelection
      (E:=AnisotropicObservationState n) (S:=Configuration n) d e 0 =
      observationRefinementProject d T := by
    funext z
    exact nativeStreamingEdgeSelection_snd d e 0 z
  calc
    (nativeStreamingEdgeObservedKernel D μ q T e r).map Prod.snd =
        ((anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map
          (nativeStreamingEdgeSelection d e 0)).map Prod.snd := by rw [hk]
    _ = (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T)).map
        (observationRefinementProject d T) := by
      rw [←Kernel.map_comp_right _ hm measurable_snd,he]
    _ = anisotropicRecordedProfileTreeKernel D μ q T :=
      anisotropicRecordedProfileTreeKernel_refinement D μ q Q d hQ hlevels T

theorem nativeStreamingEdgeObservedLaw_record_marginal
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (e : NativeStreamingEdge T) (r : Paper.Overlap)
    (hr : q (e.depth+1)≤r ∧ r≤q e.depth) :
    (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e r).map
      (fun z => (z.1,z.2.2)) = anisotropicRecordedProfileTreeLaw D μ a q T := by
  change (anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ q T e r).map
    (Prod.map id Prod.snd) = _
  rw [←Measure.compProd_map measurable_snd,nativeStreamingEdgeObservedKernel_snd D μ q hq T e r hr]
  rfl

end QuantitativeFollowup
