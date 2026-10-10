module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeMarkLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCurrentPairContinuity
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingZeroEdgeCoherence
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometry

@[expose] public section

/-! Actual endpoint collapse for an inserted edge observation. The full
original field/spin record is kept throughout every normalized mark law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def nativeStreamingEdgeParentVertex :
    {j:ℕ}→{T:FiniteTerminalGenealogy j}→NativeStreamingEdge T→FiniteCascadeRecordVertex T
  | _, _, .here T => .root T.advance
  | _, _, .child e => .child (nativeStreamingEdgeParentVertex e)
  | _, _, .left e => .left (nativeStreamingEdgeParentVertex e)
  | _, _, .right e => .right (nativeStreamingEdgeParentVertex e)

theorem nativeStreamingEdgeParentVertex_depth {j:ℕ} {T:FiniteTerminalGenealogy j}
    (e:NativeStreamingEdge T) : (nativeStreamingEdgeParentVertex e).depth=e.depth+1 := by
  induction e with
  | here T => rfl
  | child e ih => exact ih
  | left e ih => exact ih
  | right e ih => exact ih

private theorem endpoint_id_prod_map (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (q:ℕ→Paper.Overlap) {j:ℕ} (T:FiniteTerminalGenealogy j) (x:AnisotropicObservationState n) :
    (Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) x=
      (anisotropicRecordedProfileTreeKernel D μ q T x).map (fun z=>(x,z)) := by
  ext u hu
  rw [Kernel.id_prod_apply' _ x hu]
  exact (Measure.map_apply (f:=fun z=>(x,z)) (μ:=anisotropicRecordedProfileTreeKernel D μ q T x)
    (measurable_const.prodMk measurable_id) hu).symm

private theorem endpoint_advance_property (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (q:ℕ→Paper.Overlap) {j:ℕ} (T:FiniteTerminalGenealogy j)
    (P:AnisotropicObservationState n→Records (AnisotropicObservationState n) (Configuration n) T→Prop)
    (hP:MeasurableSet {z : AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T|P z.1 z.2})
    (hp:∀x,∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q T x,P x z)
    (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q T.advance x,P z.1 z.2 := by
  change ∀ᵐz∂((Kernel.id ×ₖ anisotropicRecordedProfileTreeKernel D μ q T) ∘ₖ
    anisotropicObservationTransition D μ (q (j+1)) (q j)) x,P z.1 z.2
  apply Kernel.ae_comp_of_ae_ae hP
  exact .of_forall fun y=>by
    rw [endpoint_id_prod_map]
    exact (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).mpr (hp y)

private theorem endpoint_pad_vertex_equality (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T)
    (hp : ∀x, ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q T x,
      nativeStreamingVertexState v x z = nativeStreamingVertexState w x z)
    (d : ℕ) (x : AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q (observationTreePad T d) x,
      nativeStreamingVertexState (nativeStreamingPadVertexEmbed T d v) x z =
        nativeStreamingVertexState (nativeStreamingPadVertexEmbed T d w) x z := by
  induction d generalizing x with
  | zero => exact hp x
  | succ d ih =>
      exact endpoint_advance_property D μ q (observationTreePad T d)
        (fun y z => nativeStreamingVertexState (nativeStreamingPadVertexEmbed T d v) y z =
          nativeStreamingVertexState (nativeStreamingPadVertexEmbed T d w) y z)
        (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
          (nativeStreamingVertexState_measurable _)) ih x

private theorem endpoint_left_property (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (q:ℕ→Paper.Overlap) {j:ℕ} (T U:FiniteTerminalGenealogy j)
    (P:AnisotropicObservationState n→Records (AnisotropicObservationState n) (Configuration n) T→Prop)
    (hP:MeasurableSet {z : AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) T|P z.1 z.2})
    (hp:∀x,∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q T x,P x z)
    (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q (.fork T U) x,P x z.1 := by
  change ∀ᵐz∂(anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
    anisotropicRecordedProfileTreeKernel D μ q U) x,P x z.1
  rw [Kernel.prod_apply]
  exact (Measure.ae_prod_iff_ae_ae (hP.preimage (measurable_const.prodMk measurable_fst))).mpr
    ((hp x).mono fun z hz=>.of_forall fun _=>hz)

private theorem endpoint_right_property (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure)
    (q:ℕ→Paper.Overlap) {j:ℕ} (T U:FiniteTerminalGenealogy j)
    (P:AnisotropicObservationState n→Records (AnisotropicObservationState n) (Configuration n) U→Prop)
    (hP:MeasurableSet {z : AnisotropicObservationState n×Records (AnisotropicObservationState n) (Configuration n) U|P z.1 z.2})
    (hp:∀x,∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q U x,P x z)
    (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q (.fork T U) x,P x z.2 := by
  change ∀ᵐz∂(anisotropicRecordedProfileTreeKernel D μ q T ×ₖ
    anisotropicRecordedProfileTreeKernel D μ q U) x,P x z.2
  rw [Kernel.prod_apply]
  exact (Measure.ae_prod_iff_ae_ae (hP.preimage (measurable_const.prodMk measurable_snd))).mpr
    (.of_forall fun _=>hp x)

theorem nativeStreamingRecordedKernel_edge_same_time_coherent
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap)
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T)
    (hq:q (e.depth+1)=q e.depth) (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ q T x,
      nativeStreamingVertexState (nativeStreamingEdgeParentVertex e) x z=
        nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) x z := by
  induction e generalizing x with
  | here T => exact nativeStreamingRecordedKernel_zeroEdge_coherent D μ q T hq x
  | @child j T e ih =>
      simp only [nativeStreamingEdgeParentVertex.eq_2,nativeStreamingEdgeChildVertex.eq_2,
        nativeStreamingVertexState.eq_2]
      exact endpoint_advance_property D μ q T
        (fun y z=>nativeStreamingVertexState (nativeStreamingEdgeParentVertex e) y z=
          nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) y z)
        (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
          (nativeStreamingVertexState_measurable _)) (fun y=>ih hq y) x
  | @left j T U e ih =>
      simp only [nativeStreamingEdgeParentVertex.eq_3,nativeStreamingEdgeChildVertex.eq_3,
        nativeStreamingVertexState.eq_3]
      exact endpoint_left_property D μ q T U
        (fun y z=>nativeStreamingVertexState (nativeStreamingEdgeParentVertex e) y z=
          nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) y z)
        (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
          (nativeStreamingVertexState_measurable _)) (fun y=>ih hq y) x
  | @right j T U e ih =>
      simp only [nativeStreamingEdgeParentVertex.eq_4,nativeStreamingEdgeChildVertex.eq_4,
        nativeStreamingVertexState.eq_4]
      exact endpoint_right_property D μ q T U
        (fun y z=>nativeStreamingVertexState (nativeStreamingEdgeParentVertex e) y z=
          nativeStreamingVertexState (nativeStreamingEdgeChildVertex e) y z)
        (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
          (nativeStreamingVertexState_measurable _)) (fun y=>ih hq y) x

private theorem endpoint_refined_root (d:ℕ→ℕ) {j:ℕ} (T:FiniteTerminalGenealogy j) :
    nativeStreamingRefinementVertexEmbed d T (.root T)=.root (observationRefineTree d T) := by
  cases T <;> rfl

theorem nativeStreamingInserted_child_endpoint_state
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap)
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T)
    (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ
      (nativeStreamingEdgeSchedule q e.depth (q e.depth))
      (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T) x,
      nativeStreamingVertexState
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e) x z=
      nativeStreamingVertexState
        (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeChildVertex e)) x z := by
  set_option backward.isDefEq.respectTransparency true in
    induction e generalizing x with
    | @here j T =>
        let d:=nativeStreamingEdgeSubdivision j
        let Q:=nativeStreamingEdgeSchedule q j (q j)
        let R:=observationRefineTree d T
        have hdep:observationRefinementDepth d j=j:=by
          simp [d,nativeStreamingEdgeSubdivision_depth]
        have htime:Q (observationRefinementDepth d j+1)=Q (observationRefinementDepth d j):=by
          rw [hdep]
          simp [Q,nativeStreamingEdgeSchedule]
        have H:=endpoint_advance_property D μ Q R.advance
          (fun y z=>y=z.1) (measurableSet_eq_fun measurable_fst measurable_snd.fst)
          (nativeStreamingRecordedKernel_zeroEdge_coherent D μ Q R htime) x
        have hpad {u : ℕ} (S : FiniteTerminalGenealogy u) (k : ℕ)
            (h : ∀ᵐ z ∂anisotropicRecordedProfileTreeKernel D μ Q S.advance.advance x,
              z.1 = z.2.1) :
            ∀ᵐ z ∂anisotropicRecordedProfileTreeKernel D μ Q
              (observationTreePad S (nativeStreamingEdgeSubdivision k k)).advance x,
              nativeStreamingVertexState
                (.child (.root (observationTreePad S (nativeStreamingEdgeSubdivision k k)))) x z =
              nativeStreamingVertexState
                (.child (nativeStreamingPadVertexEmbed S (nativeStreamingEdgeSubdivision k k)
                  (.root S))) x z := by
          have hkk : nativeStreamingEdgeSubdivision k k = 1 := by
            simp [nativeStreamingEdgeSubdivision]
          rw [hkk]
          simp only [observationTreePad, Nat.add_zero, nativeStreamingPadVertexEmbed,
            nativeStreamingVertexState]
          exact h
        have hembed (a : ℕ → ℕ) {u : ℕ} (S : FiniteTerminalGenealogy u) :
            nativeStreamingRefinementVertexEmbed a S.advance (.child (.root S)) =
              .child (nativeStreamingPadVertexEmbed (observationRefineTree a S) (a u)
                (.root (observationRefineTree a S))) := by
          change FiniteCascadeRecordVertex.child
            (nativeStreamingPadVertexEmbed (observationRefineTree a S) (a u)
              (nativeStreamingRefinementVertexEmbed a S (.root S))) = _
          rw [endpoint_refined_root]
        simp only [nativeStreamingEdgeChildVertex] at ⊢
        dsimp only [NativeStreamingEdge.depth, observationRefinementDepth, observationRefineTree] at ⊢
        simp only [nativeStreamingEdgeRefinedVertex.eq_1,
          nativeStreamingEdgeChildVertex.eq_1, nativeStreamingRefinementVertexEmbed.eq_2,
          hembed, endpoint_refined_root, nativeStreamingVertexState.eq_2,
          nativeStreamingVertexState.eq_1] at ⊢
        exact hpad R j H
    | @child j T e ih =>
        let d := nativeStreamingEdgeSubdivision e.depth
        let Q := nativeStreamingEdgeSchedule q e.depth (q e.depth)
        let R := observationRefineTree d T
        let v := nativeStreamingEdgeRefinedVertex d e
        let w := nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeChildVertex e)
        have hp (y : AnisotropicObservationState n) :
            ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ Q (observationTreePad R (d j)) y,
              nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) v) y z =
                nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) w) y z :=
          endpoint_pad_vertex_equality D μ Q R v w ih (d j) y
        have H := endpoint_advance_property D μ Q (observationTreePad R (d j))
          (fun y z => nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) v) y z =
            nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) w) y z)
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) hp x
        set_option backward.isDefEq.respectTransparency false in
          simpa only [d, Q, R, v, w, NativeStreamingEdge.depth, observationRefineTree,
          nativeStreamingEdgeRefinedVertex.eq_2, nativeStreamingEdgeChildVertex.eq_2,
          nativeStreamingRefinementVertexEmbed.eq_3, nativeStreamingVertexState.eq_2] using H
    | left e ih =>
        exact endpoint_left_property D μ _ _ _ _
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) ih x
    | right e ih =>
        exact endpoint_right_property D μ _ _ _ _
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) ih x

theorem nativeStreamingInserted_parent_endpoint_state
    (D:AnisotropicSpinModel n) (μ:Paper.ParisiMeasure) (q:ℕ→Paper.Overlap)
    {j:ℕ} {T:FiniteTerminalGenealogy j} (e:NativeStreamingEdge T)
    (x:AnisotropicObservationState n) :
    ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ
      (nativeStreamingEdgeSchedule q e.depth (q (e.depth+1)))
      (observationRefineTree (nativeStreamingEdgeSubdivision e.depth) T) x,
      nativeStreamingVertexState
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision e.depth) e) x z=
      nativeStreamingVertexState
        (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision e.depth) T
          (nativeStreamingEdgeParentVertex e)) x z := by
  set_option backward.isDefEq.respectTransparency true in
    induction e generalizing x with
    | @here j T =>
        let d:=nativeStreamingEdgeSubdivision j
        let Q:=nativeStreamingEdgeSchedule q j (q (j+1))
        let R:=observationRefineTree d T
        have hdep:observationRefinementDepth d j=j:=by
          simp [d,nativeStreamingEdgeSubdivision_depth]
        have htime:Q (observationRefinementDepth d j+1+1)=Q (observationRefinementDepth d j+1):=by
          rw [hdep]
          simp [Q,nativeStreamingEdgeSchedule]
        have H:∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ Q R.advance.advance x,z.1=x:=
          (nativeStreamingRecordedKernel_zeroEdge_coherent D μ Q R.advance htime x).mono
            fun _ h=>h.symm
        have hpad {u : ℕ} (S : FiniteTerminalGenealogy u) (k : ℕ)
            (h : ∀ᵐ z ∂anisotropicRecordedProfileTreeKernel D μ Q S.advance.advance x,
              z.1 = x) :
            ∀ᵐ z ∂anisotropicRecordedProfileTreeKernel D μ Q
              (observationTreePad S (nativeStreamingEdgeSubdivision k k)).advance x,
              z.1 = x := by
          have hkk : nativeStreamingEdgeSubdivision k k = 1 := by
            simp [nativeStreamingEdgeSubdivision]
          rw [hkk]
          simp only [observationTreePad, Nat.add_zero]
          exact h
        simp only [nativeStreamingEdgeParentVertex] at ⊢
        dsimp only [NativeStreamingEdge.depth, observationRefinementDepth, observationRefineTree] at ⊢
        simp only [nativeStreamingEdgeRefinedVertex.eq_1,
          endpoint_refined_root, nativeStreamingVertexState.eq_2,
          nativeStreamingVertexState.eq_1] at ⊢
        exact hpad R j H
    | @child j T e ih =>
        let d := nativeStreamingEdgeSubdivision e.depth
        let Q := nativeStreamingEdgeSchedule q e.depth (q (e.depth+1))
        let R := observationRefineTree d T
        let v := nativeStreamingEdgeRefinedVertex d e
        let w := nativeStreamingRefinementVertexEmbed d T (nativeStreamingEdgeParentVertex e)
        have hp (y : AnisotropicObservationState n) :
            ∀ᵐz∂anisotropicRecordedProfileTreeKernel D μ Q (observationTreePad R (d j)) y,
              nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) v) y z =
                nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) w) y z :=
          endpoint_pad_vertex_equality D μ Q R v w ih (d j) y
        have H := endpoint_advance_property D μ Q (observationTreePad R (d j))
          (fun y z => nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) v) y z =
            nativeStreamingVertexState (nativeStreamingPadVertexEmbed R (d j) w) y z)
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) hp x
        set_option backward.isDefEq.respectTransparency false in
          simpa only [d, Q, R, v, w, NativeStreamingEdge.depth, observationRefineTree,
          nativeStreamingEdgeRefinedVertex.eq_2, nativeStreamingEdgeParentVertex.eq_2,
          nativeStreamingRefinementVertexEmbed.eq_3, nativeStreamingVertexState.eq_2] using H
    | left e ih =>
        exact endpoint_left_property D μ _ _ _ _
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) ih x
    | right e ih =>
        exact endpoint_right_property D μ _ _ _ _
          (measurableSet_eq_fun (nativeStreamingVertexState_measurable _)
            (nativeStreamingVertexState_measurable _)) ih x

end QuantitativeFollowup
