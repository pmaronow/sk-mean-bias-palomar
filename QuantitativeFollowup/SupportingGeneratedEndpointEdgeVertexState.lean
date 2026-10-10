module
public import QuantitativeFollowup.SupportingGeneratedEndpointEdgeProjection
public import QuantitativeFollowup.SupportingNativeEdgeObservedMarginal

@[expose] public section

/-! The endpoint projection preserves every original vertex state under
the actual selected-edge law. The record marginal and zero-time identity
are proved native laws; no state-coherence conclusion is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem printedGeneratedEndpoint_edge_vertex_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (e : NativeStreamingEdge U.tree) (r : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth)
    (v : FiniteCascadeRecordVertex U.tree) :
    ∀ᵐz ∂(anisotropicObservationInitialLaw D μ a ⊗ₘ nativeStreamingEdgeObservedKernel D μ
      (nativeStreamingGeneratedEndpointClock U h) (nativeStreamingGeneratedEndpointComponent U).tree
        (printedGeneratedEndpointEdge U e) r),
    nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex U v) z.1 z.2.2 =
      nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject U z.2.2) := by
  have hq : Antitone (nativeStreamingGeneratedEndpointClock U h) := by
    simpa only [nativeStreamingGeneratedEndpointComponent_clock] using
      nativeStreamingGeneratedComponentClock_antitone (nativeStreamingGeneratedEndpointComponent U) h
  have hcell := printedGeneratedEndpointEdge_cell U e h r hr
  simp only [nativeStreamingGeneratedEndpointComponent_clock] at hcell
  have hm := nativeStreamingEdgeObservedLaw_record_marginal D μ a _ hq
    (nativeStreamingGeneratedEndpointComponent U).tree (printedGeneratedEndpointEdge U e) r hcell
  have hs := nativeStreamingGeneratedEndpoint_vertex_state D μ a U h v
  rw [←hm] at hs
  exact ae_of_ae_map (measurable_fst.prodMk measurable_snd.snd).aemeasurable hs

end QuantitativeFollowup
