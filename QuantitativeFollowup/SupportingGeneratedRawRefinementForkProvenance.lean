module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionLocations
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement

@[expose] public section

/-! An observation refinement adds only unary vertices. The complete
ordered list of actual forks is the embedded original list, so retained
fork indices and their physical depths transport without a law premise. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedRawPadForkVertices {J : ℕ} (T : FiniteTerminalGenealogy J)
    (k : ℕ) :
    cavityGeneratedOriginForkVertices (observationTreePad T k) =
      (cavityGeneratedOriginForkVertices T).map (nativeStreamingPadVertexEmbed T k) := by
  induction k with
  | zero => exact (List.map_id _).symm
  | succ k ih =>
      change (cavityGeneratedOriginForkVertices (observationTreePad T k)).map
        FiniteCascadeRecordVertex.child = _
      rw [ih, List.map_map]
      rfl

theorem cavityGeneratedRawRefinementForkVertices (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    cavityGeneratedOriginForkVertices (observationRefineTree d T) =
      (cavityGeneratedOriginForkVertices T).map (nativeStreamingRefinementVertexEmbed d T) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      change (cavityGeneratedOriginForkVertices
        (observationTreePad (observationRefineTree d T) (d j))).map
          FiniteCascadeRecordVertex.child = _
      rw [cavityGeneratedRawPadForkVertices, ih]
      simp only [cavityGeneratedOriginForkVertices, List.map_map, Function.comp_def,
        nativeStreamingRefinementVertexEmbed]
      rfl
  | fork T U ihT ihU =>
      simp only [observationRefineTree, cavityGeneratedOriginForkVertices,
        List.map_append, List.map_map, Function.comp_def, List.map_singleton,
        nativeStreamingRefinementVertexEmbed]
      rw [ihT, ihU]
      simp only [List.map_map, Function.comp_def]
      rfl

theorem cavityGeneratedRawRefinementForkCount (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    (cavityGeneratedOriginForkVertices (observationRefineTree d T)).length =
      (cavityGeneratedOriginForkVertices T).length := by
  rw [cavityGeneratedRawRefinementForkVertices, List.length_map]

theorem cavityGeneratedRawRefinementForkIndex_get (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (i : Fin (cavityGeneratedOriginForkVertices T).length) :
    (cavityGeneratedOriginForkVertices (observationRefineTree d T)).get
        (Fin.cast (cavityGeneratedRawRefinementForkCount d T).symm i) =
      nativeStreamingRefinementVertexEmbed d T ((cavityGeneratedOriginForkVertices T).get i) := by
  have h := congrArg (fun L => L[i.val]?) (cavityGeneratedRawRefinementForkVertices d T)
  rw [List.getElem?_map, List.getElem?_eq_getElem i.isLt,
    List.getElem?_eq_getElem (by
      simpa only [Fin.val_cast] using
        (Fin.cast (cavityGeneratedRawRefinementForkCount d T).symm i).isLt)] at h
  exact Option.some.inj h

theorem cavityGeneratedRawRefinementForkIndex_depth (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (i : Fin (cavityGeneratedOriginForkVertices T).length) :
    ((cavityGeneratedOriginForkVertices (observationRefineTree d T)).get
      (Fin.cast (cavityGeneratedRawRefinementForkCount d T).symm i)).depth =
      observationRefinementDepth d ((cavityGeneratedOriginForkVertices T).get i).depth := by
  rw [cavityGeneratedRawRefinementForkIndex_get, nativeStreamingRefinementVertexEmbed_depth]

theorem cavityGeneratedRawRefinementFork_mem_iff (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) (w : FiniteCascadeRecordVertex (observationRefineTree d T)) :
    w ∈ cavityGeneratedOriginForkVertices (observationRefineTree d T) ↔
      ∃ v ∈ cavityGeneratedOriginForkVertices T, nativeStreamingRefinementVertexEmbed d T v = w := by
  rw [cavityGeneratedRawRefinementForkVertices, List.mem_map]

end QuantitativeFollowup
