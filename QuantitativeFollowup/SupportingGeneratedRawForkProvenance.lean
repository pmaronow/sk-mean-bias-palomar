module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionLocations
public import FourPapersCommon.FiniteCascadeContinuationVertexGeometry

@[expose] public section

/-! Every genuine fork in an arbitrary continuation graft has a concrete
origin: an original fork, a continuation fork, or the added attachment
fork. Finite lookup computes a routing of every output fork index, and
its physical depth and clock are derived from the actual tree geometry. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def cavityGeneratedRawContinuationNewVertex
    (U : (j : ℕ) → FiniteTerminalGenealogy j) :
    {J : ℕ} → {T : FiniteTerminalGenealogy J} → (v : FiniteCascadeRecordVertex T) →
      FiniteCascadeRecordVertex (U v.depth) →
        FiniteCascadeRecordVertex (finiteCascadeContinuationGraft U v)
  | _, _, .root _, w => .right w
  | _, _, .child v, w => .child (cavityGeneratedRawContinuationNewVertex U v w)
  | _, _, .left v, w => .left (cavityGeneratedRawContinuationNewVertex U v w)
  | _, _, .right v, w => .right (cavityGeneratedRawContinuationNewVertex U v w)

@[reducible] def cavityGeneratedRawContinuationAnchor
    (U : (j : ℕ) → FiniteTerminalGenealogy j) :
    {J : ℕ} → {T : FiniteTerminalGenealogy J} → (v : FiniteCascadeRecordVertex T) →
      FiniteCascadeRecordVertex (finiteCascadeContinuationGraft U v)
  | _, _, .root _ => .root _
  | _, _, .child v => .child (cavityGeneratedRawContinuationAnchor U v)
  | _, _, .left v => .left (cavityGeneratedRawContinuationAnchor U v)
  | _, _, .right v => .right (cavityGeneratedRawContinuationAnchor U v)

theorem cavityGeneratedRawContinuationNewVertex_depth
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) (w : FiniteCascadeRecordVertex (U v.depth)) :
    (cavityGeneratedRawContinuationNewVertex U v w).depth = w.depth := by
  induction v with
  | root T => rfl
  | child v ih => exact ih w
  | left v ih => exact ih w
  | right v ih => exact ih w

theorem cavityGeneratedRawContinuationAnchor_depth
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) :
    (cavityGeneratedRawContinuationAnchor U v).depth = v.depth := by
  induction v with
  | root T => rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

/-- All actual fork vertices are classified; arbitrary repeated clock values are allowed. -/
theorem cavityGeneratedRawGraftFork_mem_classification
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (w : FiniteCascadeRecordVertex (finiteCascadeContinuationGraft U v))
    (hw : w ∈ cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)) :
    (∃z ∈ cavityGeneratedOriginForkVertices T, w = finiteCascadeContinuationVertexEmbed U v z) ∨
      (∃z ∈ cavityGeneratedOriginForkVertices (U v.depth),
        w = cavityGeneratedRawContinuationNewVertex U v z) ∨
      w = cavityGeneratedRawContinuationAnchor U v := by
  induction v with
  | root T =>
      simp only [finiteCascadeContinuationGraft,cavityGeneratedOriginForkVertices,
        List.mem_append,List.mem_map,List.mem_singleton] at hw
      rcases hw with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | rfl
      · exact .inl ⟨z,hz,rfl⟩
      · exact .inr (.inl ⟨z,hz,rfl⟩)
      · exact .inr (.inr rfl)
  | child v ih =>
      simp only [finiteCascadeContinuationGraft,cavityGeneratedOriginForkVertices,List.mem_map] at hw
      rcases hw with ⟨z,hz,rfl⟩
      rcases ih z hz with ⟨u,hu,he⟩ | ⟨u,hu,he⟩ | he
      · exact .inl ⟨.child u,List.mem_map.mpr ⟨u,hu,rfl⟩,
          congrArg FiniteCascadeRecordVertex.child he⟩
      · exact .inr (.inl ⟨u,hu,congrArg FiniteCascadeRecordVertex.child he⟩)
      · exact .inr (.inr (congrArg FiniteCascadeRecordVertex.child he))
  | @left J T R v ih =>
      simp only [finiteCascadeContinuationGraft,cavityGeneratedOriginForkVertices,
        List.mem_append,List.mem_map,List.mem_singleton] at hw
      rcases hw with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | rfl
      · rcases ih z hz with ⟨u,hu,he⟩ | ⟨u,hu,he⟩ | he
        · refine .inl ⟨.left u,?_,congrArg FiniteCascadeRecordVertex.left he⟩
          exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨u,hu,rfl⟩))
        · exact .inr (.inl ⟨u,hu,congrArg FiniteCascadeRecordVertex.left he⟩)
        · exact .inr (.inr (congrArg FiniteCascadeRecordVertex.left he))
      · refine .inl ⟨.right z,?_,rfl⟩
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨z,hz,rfl⟩))
      · refine .inl ⟨.root (.fork T R),?_,rfl⟩
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  | @right J T R v ih =>
      simp only [finiteCascadeContinuationGraft,cavityGeneratedOriginForkVertices,
        List.mem_append,List.mem_map,List.mem_singleton] at hw
      rcases hw with (⟨z,hz,rfl⟩ | ⟨z,hz,rfl⟩) | rfl
      · refine .inl ⟨.left z,?_,rfl⟩
        exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨z,hz,rfl⟩))
      · rcases ih z hz with ⟨u,hu,he⟩ | ⟨u,hu,he⟩ | he
        · refine .inl ⟨.right u,?_,congrArg FiniteCascadeRecordVertex.right he⟩
          exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨u,hu,rfl⟩))
        · exact .inr (.inl ⟨u,hu,congrArg FiniteCascadeRecordVertex.right he⟩)
        · exact .inr (.inr (congrArg FiniteCascadeRecordVertex.right he))
      · refine .inl ⟨.root (.fork T R),?_,rfl⟩
        exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

abbrev CavityGeneratedRawGraftForkOrigin
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) :=
  Fin (cavityGeneratedOriginForkVertices T).length ⊕
    (Fin (cavityGeneratedOriginForkVertices (U v.depth)).length ⊕ Unit)

/-- Concrete finite lookup, with the attachment fork as the final branch. -/
def cavityGeneratedRawGraftForkRoute
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (i : Fin (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).length) :
    CavityGeneratedRawGraftForkOrigin U v := by
  classical
  exact if ho : ∃j : Fin (cavityGeneratedOriginForkVertices T).length,
      finiteCascadeContinuationVertexEmbed U v ((cavityGeneratedOriginForkVertices T).get j) =
        (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i
    then .inl (Classical.choose ho)
    else if hn : ∃j : Fin (cavityGeneratedOriginForkVertices (U v.depth)).length,
      cavityGeneratedRawContinuationNewVertex U v ((cavityGeneratedOriginForkVertices (U v.depth)).get j) =
        (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i
      then .inr (.inl (Classical.choose hn)) else .inr (.inr ())

def cavityGeneratedRawGraftForkOriginVertex
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) : CavityGeneratedRawGraftForkOrigin U v →
      FiniteCascadeRecordVertex (finiteCascadeContinuationGraft U v)
  | .inl j => finiteCascadeContinuationVertexEmbed U v ((cavityGeneratedOriginForkVertices T).get j)
  | .inr (.inl j) => cavityGeneratedRawContinuationNewVertex U v
      ((cavityGeneratedOriginForkVertices (U v.depth)).get j)
  | .inr (.inr _) => cavityGeneratedRawContinuationAnchor U v

theorem cavityGeneratedRawGraftForkRoute_vertex
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (i : Fin (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).length) :
    cavityGeneratedRawGraftForkOriginVertex U v (cavityGeneratedRawGraftForkRoute U v i) =
      (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i := by
  classical
  unfold cavityGeneratedRawGraftForkRoute
  split_ifs with ho hn
  · exact Classical.choose_spec ho
  · exact Classical.choose_spec hn
  · have hc := cavityGeneratedRawGraftFork_mem_classification U v
      ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i)
      (List.get_mem _ i)
    rcases hc with ⟨z,hz,he⟩ | ⟨z,hz,he⟩ | he
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hz
      exact False.elim (ho ⟨j,by rw [hj]; exact he.symm⟩)
    · obtain ⟨j,hj⟩ := List.mem_iff_get.mp hz
      exact False.elim (hn ⟨j,by rw [hj]; exact he.symm⟩)
    · exact he.symm

theorem cavityGeneratedRawGraftForkRoute_depth
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (i : Fin (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).length) :
    ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i).depth =
      match cavityGeneratedRawGraftForkRoute U v i with
      | .inl j => ((cavityGeneratedOriginForkVertices T).get j).depth
      | .inr (.inl j) => ((cavityGeneratedOriginForkVertices (U v.depth)).get j).depth
      | .inr (.inr _) => v.depth := by
  rw [←cavityGeneratedRawGraftForkRoute_vertex U v i]
  generalize cavityGeneratedRawGraftForkRoute U v i = r
  rcases r with j | (j | u)
  · exact finiteCascadeContinuationVertexEmbed_depth U v _
  · exact cavityGeneratedRawContinuationNewVertex_depth U v _
  · exact cavityGeneratedRawContinuationAnchor_depth U v

theorem cavityGeneratedRawGraftForkRoute_clock
    {A : Type*} (q : ℕ → A)
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (i : Fin (cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).length) :
    q ((cavityGeneratedOriginForkVertices (finiteCascadeContinuationGraft U v)).get i).depth =
      match cavityGeneratedRawGraftForkRoute U v i with
      | .inl j => q ((cavityGeneratedOriginForkVertices T).get j).depth
      | .inr (.inl j) => q ((cavityGeneratedOriginForkVertices (U v.depth)).get j).depth
      | .inr (.inr _) => q v.depth := by
  have h := congrArg q (cavityGeneratedRawGraftForkRoute_depth U v i)
  generalize cavityGeneratedRawGraftForkRoute U v i = r at h ⊢
  rcases r with j | (j | u) <;> exact h

end QuantitativeFollowup
