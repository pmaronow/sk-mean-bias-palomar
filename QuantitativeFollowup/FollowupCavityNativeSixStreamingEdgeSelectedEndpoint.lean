module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeEndpointCoherenceLaws
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometry

@[expose] public section

/-! Every exact observation refinement has the actual child state at a
selected child-endpoint clock. The selected-state/whole-record law is
identified with the genuine one-slot law before transferring its AE equality. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem selectedEndpoint_block_last {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) (hd : d=p+1) :
    nativeStreamingBlockSelectedVertexAt T d p =
      .child (.root (observationTreePad T d)) := by
  subst d
  simp only [nativeStreamingBlockSelectedVertexAt,if_true,observationTreePad]

theorem nativeStreamingSelected_one_slot_vertex
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) :
    nativeStreamingEdgeSelectedVertex (nativeStreamingEdgeSubdivision e.depth) e 0 =
      nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e := by
  induction e with
  | @here j T =>
      simp only [NativeStreamingEdge.depth,nativeStreamingEdgeSelectedVertex,
        nativeStreamingEdgeRefinedVertex]
      exact selectedEndpoint_block_last _ _ 0 (if_pos rfl)
  | child e ih =>
      simp only [NativeStreamingEdge.depth,nativeStreamingEdgeSelectedVertex,
        nativeStreamingEdgeRefinedVertex,ih]
  | left e ih =>
      simp only [NativeStreamingEdge.depth,nativeStreamingEdgeSelectedVertex,
        nativeStreamingEdgeRefinedVertex,ih]
  | right e ih =>
      simp only [NativeStreamingEdge.depth,nativeStreamingEdgeSelectedVertex,
        nativeStreamingEdgeRefinedVertex,ih]

theorem nativeStreamingSelected_child_endpoint_state
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hq : Antitone q) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j)=q j)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth)
    (hmark : Q (observationRefinementDepth d e.depth+p+1)=q e.depth)
    (x : AnisotropicObservationState n) :
    ∀ᵐz ∂anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T) x,
      nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) x z =
        nativeStreamingVertexState (nativeStreamingRefinementVertexEmbed d T
          (nativeStreamingEdgeChildVertex e)) x z := by
  let d0 := nativeStreamingEdgeSubdivision e.depth
  let Q0 := nativeStreamingEdgeSchedule q e.depth (q e.depth)
  have hQ0 : Antitone Q0 := nativeStreamingEdgeSchedule_antitone q hq e.depth (q e.depth)
    ⟨hq (Nat.le_succ e.depth),le_rfl⟩
  have hp0 : 0<d0 e.depth := by simp [d0,nativeStreamingEdgeSubdivision]
  have hmark0 : Q0 (observationRefinementDepth d0 e.depth+0+1)=q e.depth := by
    simp [Q0,d0,nativeStreamingEdgeSubdivision_depth,nativeStreamingEdgeSchedule]
  let P : (AnisotropicObservationState n ×
    Records (AnisotropicObservationState n) (Configuration n) T) → Prop := fun y => y.1 =
    nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) x y.2
  have hP : MeasurableSet {y | P y} := measurableSet_eq_fun measurable_fst
    ((nativeStreamingVertexState_measurable (nativeStreamingEdgeChildVertex e)).comp
      (measurable_const.prodMk measurable_snd))
  have hm0 := measurable_nativeStreamingEdgeSelection
    (E := AnisotropicObservationState n) (S := Configuration n) d0 e 0
  have hm := measurable_nativeStreamingEdgeSelection
    (E := AnisotropicObservationState n) (S := Configuration n) d e p
  have he0 : (anisotropicRecordedProfileTreeKernel D μ Q0 (observationRefineTree d0 T) x).map
      (nativeStreamingEdgeSelection d0 e 0) = nativeStreamingEdgeObservedKernel D μ q T e (q e.depth) x := by
    rw [←Kernel.map_apply _ hm0,nativeStreamingEdgeSelection_kernel D μ q Q0 d0 hQ0
      (nativeStreamingEdgeSchedule_refinement q e.depth (q e.depth)) e 0 hp0,hmark0]
  have he : (anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T) x).map
      (nativeStreamingEdgeSelection d e p) = nativeStreamingEdgeObservedKernel D μ q T e (q e.depth) x := by
    rw [←Kernel.map_apply _ hm,nativeStreamingEdgeSelection_kernel D μ q Q d hQ hlevels e p hp,hmark]
  have hs0 : ∀ᵐz ∂anisotropicRecordedProfileTreeKernel D μ Q0 (observationRefineTree d0 T) x,
      P (nativeStreamingEdgeSelection d0 e 0 z) := by
    have H := nativeStreamingInserted_child_endpoint_state D μ q e x
    filter_upwards [H] with z hz
    change (nativeStreamingEdgeSelection d0 e 0 z).1 =
      nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) x
        (nativeStreamingEdgeSelection d0 e 0 z).2
    rw [←nativeStreamingEdgeSelectedVertex_state,nativeStreamingSelected_one_slot_vertex,
      nativeStreamingEdgeSelection_snd]
    exact hz.trans (nativeStreamingRefinementVertexEmbed_state d0 T
      (nativeStreamingEdgeChildVertex e) x z)
  have hs : ∀ᵐy ∂nativeStreamingEdgeObservedKernel D μ q T e (q e.depth) x, P y := by
    rw [←he0]
    exact (ae_map_iff hm0.aemeasurable hP).mpr hs0
  have H : ∀ᵐz ∂anisotropicRecordedProfileTreeKernel D μ Q (observationRefineTree d T) x,
      P (nativeStreamingEdgeSelection d e p z) := by
    apply (ae_map_iff hm.aemeasurable hP).mp
    rw [he]
    exact hs
  filter_upwards [H] with z hz
  rw [nativeStreamingEdgeSelectedVertex_state,nativeStreamingRefinementVertexEmbed_state]
  simpa only [P,nativeStreamingEdgeSelection_snd] using hz

end QuantitativeFollowup
