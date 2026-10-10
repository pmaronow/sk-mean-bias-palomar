module
public import QuantitativeFollowup.SupportingPrintedCoalescedOriginWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternVertexCoherence
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherence

@[expose] public section

/-! Structural passage from genuine all-edge and fork-root coherence to
the recursive coalesced-origin condition. Repeated cells stay in the tree. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128

theorem nativeCoalescedOriginCoherent_of_edges_root_coherent
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (Φ : NativeStreamingOrigin T → ℝ)
    (hroot : nativeStreamingRootCoherent T (fun v => Φ (.vertex v)))
    (hzero : ∀ e : NativeStreamingEdge T, q (e.depth+1)=q e.depth →
      Φ (.vertex (nativeStreamingEdgeChildVertex e)) =
        Φ (.vertex (nativeStreamingEdgeParentVertex e)))
    (hend : ∀ e : NativeStreamingEdge T, Φ (.edge e (q e.depth)) =
      Φ (.vertex (nativeStreamingEdgeChildVertex e)))
    (hi : ∀ e : NativeStreamingEdge T,
      IntegrableOn (fun r => Φ (.edge e r)) (Ioc (q (e.depth+1)) (q e.depth))
        (parisiFreeMeasure μ a)) :
    nativeCoalescedOriginCoherent μ a q T Φ := by
  induction T with
  | leaf => trivial
  | @advance j T ih =>
      refine ⟨?_, hi (.here T), ?_⟩
      · split_ifs with hz
        · exact hzero (.here T) hz
        · exact hend (.here T)
      · exact ih (fun o => Φ (nativeStreamingOriginChild o)) hroot
          (fun e he => hzero (.child e) he)
          (fun e => hend (.child e)) (fun e => hi (.child e))
  | @fork j T U ihT ihU =>
      exact ⟨hroot.1, hroot.2.1,
        ihT (fun o => Φ (nativeStreamingOriginLeft o)) hroot.2.2.1
          (fun e he => hzero (.left e) he)
          (fun e => hend (.left e)) (fun e => hi (.left e)),
        ihU (fun o => Φ (nativeStreamingOriginRight o)) hroot.2.2.2
          (fun e he => hzero (.right e) he)
          (fun e => hend (.right e)) (fun e => hi (.right e))⟩

end QuantitativeFollowup
