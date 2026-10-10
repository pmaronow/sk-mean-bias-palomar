module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingFuturePairLaw
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Endpoint padding preserves the actual ancestral field and its clock.
The future transition and both independent terminal draws therefore
project with the entire old record to the original future marked law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem nativeStreamingGeneratedEndpoint_future_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex U.tree) (l : Paper.Overlap) :
    nativeStreamingFuturePairKernel D μ (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree (nativeStreamingGeneratedEndpointVertex U v) l =ᵐ[
        anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock U h)
          (nativeStreamingGeneratedEndpointComponent U).tree]
      (nativeStreamingFuturePairKernel D μ (nativeStreamingGeneratedComponentClock U h) U.tree v l).comap
        (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U))
        (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)) := by
  filter_upwards [nativeStreamingGeneratedEndpoint_vertex_state D μ a U h v] with z hz
  change ((anisotropicObservationTerminalSpinKernel D μ l ×ₖ
      anisotropicObservationTerminalSpinKernel D μ l) ∘ₖ anisotropicObservationTransition D μ
      (nativeStreamingGeneratedEndpointClock U h (nativeStreamingGeneratedEndpointVertex U v).depth) l)
      (nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex U v) z.1 z.2) =
    ((anisotropicObservationTerminalSpinKernel D μ l ×ₖ
      anisotropicObservationTerminalSpinKernel D μ l) ∘ₖ anisotropicObservationTransition D μ
      (nativeStreamingGeneratedComponentClock U h v.depth) l)
      (nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject U z.2))
  rw [nativeStreamingGeneratedEndpointVertex_depth,nativeStreamingGeneratedEndpointClock_succ,hz]

theorem nativeStreamingGeneratedEndpoint_future_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex U.tree) (l : Paper.Overlap) :
    (nativeStreamingFuturePairLaw D μ a (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree (nativeStreamingGeneratedEndpointVertex U v) l).map
        (Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)) id) =
      nativeStreamingFuturePairLaw D μ a (nativeStreamingGeneratedComponentClock U h) U.tree v l := by
  unfold nativeStreamingFuturePairLaw
  rw [Measure.compProd_congr (nativeStreamingGeneratedEndpoint_future_kernel D μ a U h v l)]
  have he := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree)
    (Prod.map id (nativeStreamingGeneratedEndpointRecordProject U))
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U))
    (nativeStreamingFuturePairKernel D μ (nativeStreamingGeneratedComponentClock U h) U.tree v l)
  rw [nativeStreamingGeneratedEndpoint_record_law] at he
  exact he

end QuantitativeFollowup
