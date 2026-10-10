module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginFamilies
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedMixedCrossPatternsTerminal
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsLaw
public import QuantitativeFollowup.FollowupCavityGeneratedForestComponentReplacementRetained

@[expose] public section

/-! Exact clocks of the concrete two-origin charts. Mixed continuations copy
an arbitrary genuine interior vertex, including a padded original root. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def printedGeneratedOriginCrossChartOrigin (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (r : Paper.Overlap) : NativeStreamingOrigin U.tree :=
  match γ with
  | .inl i => .vertex (printedGeneratedOriginChartFork U i)
  | .inr (.inl i) => .edge (printedGeneratedOriginChartEdge U i) r
  | .inr (.inr _) => .vertex (.root U.tree)

theorem printedGeneratedCrossVertexAppend_physical
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    nativeStreamingGeneratedCrossVertexAppend U v w h =
      (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
        (nativeStreamingGeneratedComponentClock U h w.depth) :
          CavityGeneratedHistory Paper.Overlap (m+2)) := by
  unfold nativeStreamingGeneratedCrossVertexAppend
  rw [nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh v.depth,
    nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh w.depth]

theorem printedGeneratedMixedCrossClock_physical
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ)
      (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth)) =
        nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h) e.depth r := by
  let A := nativeStreamingGeneratedEdgeComponent U e .single
  let z := nativeStreamingGeneratedMixedAttachedVertex U e v
  have hz := nativeStreamingGeneratedMixedAttachedVertex_interior U e v hv0 hvJ
  have ho := printedGeneratedEdgeComponent_snoc_order U e .single h r hh hr
  have hc : (cavityGeneratedFiniteClockLabels A.label z.depth).value (Fin.snoc h r) =
      nativeStreamingGeneratedComponentClock U h v.depth := by
    change (cavityGeneratedFiniteClockLabels (nativeStreamingGeneratedEdgeLabels U e)
      (finiteCascadeContinuationVertexEmbed observationLinearTree
        (nativeStreamingGeneratedEdgeVertex U e) (nativeStreamingGeneratedMixedRefinedVertex U e v)).depth).value
        (Fin.snoc h r) = _
    rw [finiteCascadeContinuationVertexEmbed_depth, nativeStreamingGeneratedMixedRefinedVertex_depth,
      nativeStreamingGeneratedEdgeLabels_global, nativeStreamingGeneratedEdgeGlobalLabels_refinement,
      CavityGeneratedClockLabel.append_reindex_value, cavityGeneratedHistoryPrefix_snoc]
    exact nativeStreamingGeneratedComponent_raw_eq_clock_of_order U h hh v.depth
  change nativeStreamingGeneratedComponentClock
    (nativeStreamingGeneratedVertexComponent A z hz.1 hz.2 .single)
      (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth)) = _
  rw [←hc, nativeStreamingGeneratedVertexComponent_clock_at_atom,
    nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc U e h r hh hr]

theorem printedGeneratedComponentReindex_clock
    (U : CavityGeneratedConstructedComponent m) {k : ℕ} (τ : Fin m → Fin k)
    (H : CavityGeneratedHistory Paper.Overlap k) :
    nativeStreamingGeneratedComponentClock (printedGeneratedComponentReindex U τ) H =
      nativeStreamingGeneratedComponentClock U (H ∘ τ) := by
  apply congrArg cavityGeneratedClippedClock
  funext j
  exact printedGeneratedComponentReindex_raw U τ (H ∘ τ) H (fun _ => rfl) j

theorem printedGeneratedCrossSwapClock_append
    (U : CavityGeneratedConstructedComponent (m+2))
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) :
    nativeStreamingGeneratedComponentClock (printedGeneratedCrossSwapComponent U)
      (Fin.snoc (Fin.snoc h r) l) =
      nativeStreamingGeneratedComponentClock U (Fin.snoc (Fin.snoc h l) r) := by
  rw [printedGeneratedCrossSwapComponent, printedGeneratedComponentReindex_clock]
  congr 1
  funext i
  exact printedGeneratedCrossSwapIndex_append h r l i

end QuantitativeFollowup
