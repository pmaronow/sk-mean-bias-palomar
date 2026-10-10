module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingZeroEdgeCoherence
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Unary endpoint observations use the actual identity transition. Their
full record law projects to the original native law, and every copied old
vertex has the same conditional single/current terminal-mark law. -/
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

theorem nativeStreamingGeneratedEndpoint_shifted_kernels
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (fun j => anisotropicObservationTransition D μ
      (nativeStreamingGeneratedEndpointClock W h (j+1)) (nativeStreamingGeneratedEndpointClock W h j)) =
    observationTerminalUnaryKernels (fun j => anisotropicObservationTransition D μ
      (nativeStreamingGeneratedComponentClock W h (j+1)) (nativeStreamingGeneratedComponentClock W h j)) := by
  funext j
  cases j with
  | zero =>
      rw [nativeStreamingGeneratedEndpointClock_duplicate_terminal,anisotropicObservationTransition_same_time]
  | succ j =>
      rw [nativeStreamingGeneratedEndpointClock_succ,nativeStreamingGeneratedEndpointClock_succ]

theorem nativeStreamingGeneratedEndpoint_lift_kernel_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeKernel D μ (nativeStreamingGeneratedEndpointClock W h)
      (observationTerminalUnaryLift W.tree)).map (observationTerminalUnaryProject W.tree) =
        anisotropicRecordedProfileTreeKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree := by
  rw [nativeStreamingRecordedProfileTreeKernel_eq_observation,
    nativeStreamingRecordedProfileTreeKernel_eq_observation,
    nativeStreamingGeneratedEndpoint_shifted_kernels]
  exact observationTreeKernel_terminalUnaryLift _ (fun _ => inferInstance) _ W.tree

@[reducible] def nativeStreamingGeneratedEndpointRecordProject {E S : Type}
    (W : CavityGeneratedConstructedComponent m) :
    Records E S (nativeStreamingGeneratedEndpointComponent W).tree → Records E S W.tree :=
  observationTerminalUnaryProject W.tree ∘ Prod.snd

theorem measurable_nativeStreamingGeneratedEndpointRecordProject {E S : Type}
    [MeasurableSpace E] [MeasurableSpace S] (W : CavityGeneratedConstructedComponent m) :
    Measurable (nativeStreamingGeneratedEndpointRecordProject (E:=E) (S:=S) W) :=
  (measurable_observationTerminalUnaryProject W.tree).comp measurable_snd

theorem nativeStreamingGeneratedEndpoint_kernel_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeKernel D μ (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree).map (nativeStreamingGeneratedEndpointRecordProject W) =
        anisotropicRecordedProfileTreeKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree := by
  change (anisotropicRecordedProfileTreeKernel D μ (nativeStreamingGeneratedEndpointClock W h)
    (observationTerminalUnaryLift W.tree).advance).map (observationTerminalUnaryProject W.tree ∘ Prod.snd) = _
  rw [nativeStreamingRecordedKernel_zeroEdge_eq D μ _ (observationTerminalUnaryLift W.tree)
    (nativeStreamingGeneratedEndpointClock_duplicate_initial W h),
    Kernel.map_comp_right _ measurable_snd (measurable_observationTerminalUnaryProject W.tree),
    ←Kernel.snd_eq,Kernel.snd_prod,nativeStreamingGeneratedEndpoint_lift_kernel_law]

theorem nativeStreamingGeneratedEndpoint_record_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree).map
        (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W)) =
      anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree := by
  rw [anisotropicRecordedProfileTreeLaw,anisotropicRecordedProfileTreeLaw,
    ←Measure.compProd_map (measurable_nativeStreamingGeneratedEndpointRecordProject W),
    nativeStreamingGeneratedEndpoint_kernel_law]

theorem nativeStreamingGeneratedEndpoint_vertex_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    ∀ᵐ z ∂anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree,
    nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex W v) z.1 z.2 =
      nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject W z.2) := by
  filter_upwards [nativeStreamingRecordedLaw_zeroEdge_coherent D μ a _
    (observationTerminalUnaryLift W.tree) (nativeStreamingGeneratedEndpointClock_duplicate_initial W h)] with z hz
  change nativeStreamingVertexState (nativeStreamingEndpointLiftVertex v) z.2.1 z.2.2 =
    nativeStreamingVertexState v z.1 (observationTerminalUnaryProject W.tree z.2.2)
  rw [←hz,nativeStreamingEndpointLiftVertex_state]

theorem nativeStreamingGeneratedEndpoint_single_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    nativeStreamingSingleVertexKernel D μ (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v) =ᵐ[
        anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
          (nativeStreamingGeneratedEndpointComponent W).tree]
      (nativeStreamingSingleVertexKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree v).comap
        (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W))
        (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject W)) := by
  filter_upwards [nativeStreamingGeneratedEndpoint_vertex_state D μ a W h v] with z hz
  change anisotropicObservationTerminalSpinKernel D μ
    (nativeStreamingGeneratedEndpointClock W h (nativeStreamingGeneratedEndpointVertex W v).depth)
    (nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex W v) z.1 z.2) =
      anisotropicObservationTerminalSpinKernel D μ (nativeStreamingGeneratedComponentClock W h v.depth)
        (nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject W z.2))
  rw [nativeStreamingGeneratedEndpointVertex_depth,nativeStreamingGeneratedEndpointClock_succ,hz]

theorem nativeStreamingGeneratedEndpoint_current_kernel
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    nativeStreamingCurrentPairKernel D μ (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v) =ᵐ[
        anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
          (nativeStreamingGeneratedEndpointComponent W).tree]
      (nativeStreamingCurrentPairKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree v).comap
        (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W))
        (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject W)) := by
  filter_upwards [nativeStreamingGeneratedEndpoint_vertex_state D μ a W h v] with z hz
  change (anisotropicObservationTerminalSpinKernel D μ
      (nativeStreamingGeneratedEndpointClock W h (nativeStreamingGeneratedEndpointVertex W v).depth) ×ₖ
    anisotropicObservationTerminalSpinKernel D μ
      (nativeStreamingGeneratedEndpointClock W h (nativeStreamingGeneratedEndpointVertex W v).depth))
      (nativeStreamingVertexState (nativeStreamingGeneratedEndpointVertex W v) z.1 z.2) =
    (anisotropicObservationTerminalSpinKernel D μ (nativeStreamingGeneratedComponentClock W h v.depth) ×ₖ
      anisotropicObservationTerminalSpinKernel D μ (nativeStreamingGeneratedComponentClock W h v.depth))
        (nativeStreamingVertexState v z.1 (nativeStreamingGeneratedEndpointRecordProject W z.2))
  rw [nativeStreamingGeneratedEndpointVertex_depth,nativeStreamingGeneratedEndpointClock_succ,hz]

theorem nativeStreamingGeneratedEndpoint_single_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingSingleVertexLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v)).map
        (Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W)) id) =
      nativeStreamingSingleVertexLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v := by
  unfold nativeStreamingSingleVertexLaw
  rw [Measure.compProd_congr (nativeStreamingGeneratedEndpoint_single_kernel D μ a W h v)]
  have he := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree)
    (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W))
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject W))
    (nativeStreamingSingleVertexKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree v)
  rw [nativeStreamingGeneratedEndpoint_record_law] at he
  exact he

theorem nativeStreamingGeneratedEndpoint_current_law
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingCurrentPairLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree (nativeStreamingGeneratedEndpointVertex W v)).map
        (Prod.map (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W)) id) =
      nativeStreamingCurrentPairLaw D μ a (nativeStreamingGeneratedComponentClock W h) W.tree v := by
  unfold nativeStreamingCurrentPairLaw
  rw [Measure.compProd_congr (nativeStreamingGeneratedEndpoint_current_kernel D μ a W h v)]
  have he := compProd_comap_map_history
    (anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock W h)
      (nativeStreamingGeneratedEndpointComponent W).tree)
    (Prod.map id (nativeStreamingGeneratedEndpointRecordProject W))
    (measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject W))
    (nativeStreamingCurrentPairKernel D μ (nativeStreamingGeneratedComponentClock W h) W.tree v)
  rw [nativeStreamingGeneratedEndpoint_record_law] at he
  exact he

end QuantitativeFollowup
