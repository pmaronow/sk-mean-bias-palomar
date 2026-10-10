module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEdgePatternsGeometry

@[expose] public section

/-! The genuine grafted continuation probability, after retaining the whole
old record and its fresh terminal mark(s), is the native edge-origin law.
The continuation probability is itself the actual enlarged recorded-tree
probability pushed through the explicit graft extraction. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem nativeStreamingGeneratedEdge_single_marked_record_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    (nativeStreamingActualContinuationProbability D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e .single)
        (Fin.snoc h r)) NativeStreamingGeneratedVertexKind.single.continuation
      NativeStreamingGeneratedVertexKind.single.recordMark
      (nativeStreamingGeneratedEdgeObservedComponent W e).tree (nativeStreamingGeneratedEdgeVertex W e)).map
        (fun z => ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth)
          W.tree z.1.2),z.2)) =
      nativeStreamingOriginSingleProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) := by
  rw [nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]
  rfl

theorem nativeStreamingGeneratedEdge_current_marked_record_projection
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge W.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h∈nativeStreamingGeneratedComponentOrderSet W)
    (hr : nativeStreamingGeneratedComponentClock W h (e.depth+1)≤r ∧
      r≤nativeStreamingGeneratedComponentClock W h e.depth) :
    (nativeStreamingActualContinuationProbability D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEdgeComponent W e .current)
        (Fin.snoc h r)) NativeStreamingGeneratedVertexKind.current.continuation
      NativeStreamingGeneratedVertexKind.current.recordMark
      (nativeStreamingGeneratedEdgeObservedComponent W e).tree (nativeStreamingGeneratedEdgeVertex W e)).map
        (fun z => ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth)
          W.tree z.1.2),z.2)) =
      nativeStreamingOriginCurrentProbability D μ a (nativeStreamingGeneratedComponentClock W h)
        W.tree (.edge e r) := by
  rw [nativeStreamingGeneratedEdgeComponent_clock,
    nativeStreamingGeneratedEdgeObservedComponent_clock_snoc W e h r hh hr]
  rfl

end QuantitativeFollowup
