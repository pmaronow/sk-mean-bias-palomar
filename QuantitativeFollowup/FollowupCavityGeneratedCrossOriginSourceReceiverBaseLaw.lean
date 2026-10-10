module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverProjection
public import FourPapersCommon.CompProdComapMap

@[expose] public section

/-! Actual whole-record laws of retained and endpoint-padded vertex charts,
and mixed charts at arbitrary copied interior vertices. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem printedGeneratedCrossVertex_full_record_law_physical
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (v w : FiniteCascadeRecordVertex U.tree)
    (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (hw0 : 0 < w.depth) (hwJ : w.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ)
        (Fin.snoc (Fin.snoc h (nativeStreamingGeneratedComponentClock U h v.depth))
          (nativeStreamingGeneratedComponentClock U h w.depth)))
      (nativeStreamingGeneratedCrossVertexComponent U v w hv0 hvJ hw0 hwJ).tree).map
        (printedGeneratedCrossVertexRecordProjection U v w hv0 hvJ hw0 hwJ) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.vertex v) (.vertex w) : Measure _) := by
  rw [nativeStreamingOriginCrossProbability_vertex_vertex D μ a _
    (nativeStreamingGeneratedComponentClock_antitone U h)
    (nativeStreamingGeneratedComponentClock_terminal U h)]
  have H := nativeStreamingGeneratedCrossVertex_full_record_law D μ a U v w hv0 hvJ hw0 hwJ h
  rw [printedGeneratedCrossVertexAppend_physical U v w h hh] at H
  exact H

theorem printedGeneratedMixedCross_full_record_law_physical
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (v : FiniteCascadeRecordVertex U.tree) (hv0 : 0 < v.depth) (hvJ : v.depth < U.depth)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    (anisotropicRecordedProfileTreeLaw D μ a
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ)
        (Fin.snoc (Fin.snoc h r) (nativeStreamingGeneratedComponentClock U h v.depth)))
      (nativeStreamingGeneratedMixedCrossComponent U e v hv0 hvJ).tree).map
        (nativeStreamingGeneratedMixedCrossRecordProjection U e v hv0 hvJ) =
      (nativeStreamingOriginCrossProbability D μ a (nativeStreamingGeneratedComponentClock U h)
        U.tree (.edge e r) (.vertex v) : Measure _) := by
  rw [printedGeneratedMixedCrossClock_physical U e v hv0 hvJ h r hh hr]
  let q := nativeStreamingGeneratedComponentClock U h
  let Q := nativeStreamingEdgeSchedule q e.depth r
  let t := nativeStreamingGeneratedEdgeVertex U e
  let w := nativeStreamingGeneratedMixedRefinedVertex U e v
  let R := nativeStreamingGeneratedEdgeObservedComponent U e
  let ψ := fun z : AnisotropicObservationState n ×
      Records (AnisotropicObservationState n) (Configuration n)
        (finiteCascadeCrossContinuationGraft observationLinearTree t w) =>
      ((z.1,(finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin t w z.2).1),
        (finiteCascadeCrossContinuationExtract observationLinearTree observationLinearSpin t w z.2).2)
  let π := fun z : CavityGeneratedCrossOriginalRecordPair (AnisotropicObservationState n) (Configuration n) R =>
      ((z.1.1,observationRefinementProject (nativeStreamingEdgeSubdivision e.depth) U.tree z.1.2),z.2)
  have hψ : Measurable ψ := by
    have hx := measurable_finiteCascadeCrossContinuationExtract (E:=AnisotropicObservationState n)
      (S:=Configuration n) observationLinearTree observationLinearSpin
      (fun j=>measurable_observationLinearSpin j) t w
    exact (measurable_fst.prodMk (hx.fst.comp measurable_snd)).prodMk (hx.snd.comp measurable_snd)
  have hπ : Measurable π :=
    (measurable_fst.fst.prodMk ((measurable_observationRefinementProject
      (nativeStreamingEdgeSubdivision e.depth) U.tree).comp measurable_fst.snd)).prodMk measurable_snd
  have hQ : Antitone Q := nativeStreamingEdgeSchedule_antitone q
    (nativeStreamingGeneratedComponentClock_antitone U h) e.depth r hr
  have hQ0 : Q 0=1 := by
    simp only [Q,nativeStreamingEdgeSchedule,Nat.zero_le,if_true]
    exact nativeStreamingGeneratedComponentClock_terminal U h
  have H := congrArg (fun M : Measure (CavityGeneratedCrossOriginalRecordPair
      (AnisotropicObservationState n) (Configuration n) R)=>M.map π)
    (nativeStreamingCrossVertexLaw_eq_graft D μ a Q hQ hQ0 R.tree t w)
  rw [Measure.map_map hπ hψ] at H
  change _ = (nativeStreamingCrossVertexProbability D μ a Q R.tree t w : Measure _).map π
  rw [nativeStreamingCrossVertexProbability_eq_law D μ a Q hQ hQ0]
  exact H

theorem printedGeneratedEndpointCrossVertexLaw_project
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (U : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m)
    (v w : FiniteCascadeRecordVertex U.tree) :
    (nativeStreamingCrossVertexLaw D μ a (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree
      (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w)).map
        (printedGeneratedEndpointCrossRecordProject U) =
      nativeStreamingCrossVertexLaw D μ a (nativeStreamingGeneratedComponentClock U h) U.tree v w := by
  let L := anisotropicRecordedProfileTreeLaw D μ a (nativeStreamingGeneratedEndpointClock U h)
    (nativeStreamingGeneratedEndpointComponent U).tree
  let π : (AnisotropicObservationState n × Records (AnisotropicObservationState n)
      (Configuration n) (nativeStreamingGeneratedEndpointComponent U).tree) →
      (AnisotropicObservationState n × Records (AnisotropicObservationState n) (Configuration n) U.tree) :=
    Prod.map id (nativeStreamingGeneratedEndpointRecordProject U)
  have hπ : Measurable π :=
    measurable_id.prodMap (measurable_nativeStreamingGeneratedEndpointRecordProject U)
  have hk : nativeStreamingCrossVertexKernel D μ (nativeStreamingGeneratedEndpointClock U h)
      (nativeStreamingGeneratedEndpointComponent U).tree
      (nativeStreamingGeneratedEndpointVertex U v) (nativeStreamingGeneratedEndpointVertex U w) =ᵐ[L]
      (nativeStreamingCrossVertexKernel D μ (nativeStreamingGeneratedComponentClock U h) U.tree v w).comap π hπ := by
    filter_upwards [nativeStreamingGeneratedEndpoint_single_kernel D μ a U h v,
      nativeStreamingGeneratedEndpoint_single_kernel D μ a U h w] with z hv hw
    simp only [nativeStreamingCrossVertexKernel, Kernel.prod_apply, Kernel.comap_apply] at *
    rw [hv,hw]
  unfold nativeStreamingCrossVertexLaw
  rw [Measure.compProd_congr hk]
  have H := compProd_comap_map_history L π hπ
    (nativeStreamingCrossVertexKernel D μ (nativeStreamingGeneratedComponentClock U h) U.tree v w)
  rw [nativeStreamingGeneratedEndpoint_record_law] at H
  exact H

end QuantitativeFollowup
