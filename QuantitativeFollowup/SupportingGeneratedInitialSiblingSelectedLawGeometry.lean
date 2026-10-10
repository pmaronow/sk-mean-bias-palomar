module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingErasure
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOrigin

@[expose] public section

/-! An initial selected vertex retains its physical level when unary
observations are erased. Levels below the common sibling fork use the
canonical root edge; equality retains the actual erased selected subtree;
levels above it use the genuine descendant leaf edge. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

@[reducible] def printedGeneratedInitialFirstLeaf :
    {J : ℕ} → (T : FiniteTerminalGenealogy J) → ObservationLeaf T
  | _, .leaf => PUnit.unit
  | _, .advance T => printedGeneratedInitialFirstLeaf T
  | _, .fork T _ => Sum.inl (printedGeneratedInitialFirstLeaf T)

@[reducible] def printedGeneratedInitialFirstDescendantLeaf :
    {J : ℕ} → {T : FiniteTerminalGenealogy J} →
      FiniteCascadeRecordVertex T → ObservationLeaf T
  | _, _, .root T => printedGeneratedInitialFirstLeaf T
  | _, _, @FiniteCascadeRecordVertex.child j T v =>
      @printedGeneratedInitialFirstDescendantLeaf j T v
  | _, _, @FiniteCascadeRecordVertex.left j T U v =>
      Sum.inl (@printedGeneratedInitialFirstDescendantLeaf j T v)
  | _, _, @FiniteCascadeRecordVertex.right j T U v =>
      Sum.inr (@printedGeneratedInitialFirstDescendantLeaf j U v)

@[reducible] def printedGeneratedInitialSiblingVertexErase :
    {J : ℕ} → {T : FiniteTerminalGenealogy J} →
      FiniteCascadeRecordVertex T →
        FiniteCascadeRecordVertex (printedGeneratedInitialSiblingErasure T).tree
  | _, _, .root T => .root (printedGeneratedInitialSiblingErasure T).tree
  | _, _, @FiniteCascadeRecordVertex.child j T v =>
      @printedGeneratedInitialSiblingVertexErase j T v
  | _, _, @FiniteCascadeRecordVertex.left j T U v =>
      .left (@printedGeneratedInitialSiblingVertexErase j T v)
  | _, _, @FiniteCascadeRecordVertex.right j T U v =>
      .right (@printedGeneratedInitialSiblingVertexErase j U v)

theorem printedGeneratedInitialSiblingVertexErase_depth
    {J : ℕ} {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) :
    (printedGeneratedInitialSiblingVertexErase v).depth = 1 := by
  induction v with
  | root T => rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

@[reducible] def printedGeneratedSiblingLeafEdge :
    (S : CavityGeneratedSiblingShape) → ObservationLeaf S.tree → NativeStreamingEdge S.tree
  | .single => fun _ => .here .leaf
  | .fork S U => fun i => by
      change ObservationLeaf (.fork S.tree U.tree) at i
      cases i with
      | inl i => exact .left (printedGeneratedSiblingLeafEdge S i)
      | inr i => exact .right (printedGeneratedSiblingLeafEdge U i)

theorem printedGeneratedSiblingLeafEdge_depth
    (S : CavityGeneratedSiblingShape) (i : ObservationLeaf S.tree) :
    (printedGeneratedSiblingLeafEdge S i).depth = 0 := by
  induction S with
  | single => rfl
  | fork S U ihS ihU => cases i with
    | inl i => exact ihS i
    | inr i => exact ihU i

@[reducible] def printedGeneratedInitialSiblingSelectedOrigin
    {J : ℕ} (T : FiniteTerminalGenealogy J) (p r : Paper.Overlap)
    (v : FiniteCascadeRecordVertex T) :
    NativeStreamingOrigin (.advance (printedGeneratedInitialSiblingErasure T).tree) := by
  classical
  exact if r < p then .edge (.here (printedGeneratedInitialSiblingErasure T).tree) r
    else if r = p then .vertex (.child (printedGeneratedInitialSiblingVertexErase v))
    else .edge (.child (printedGeneratedSiblingLeafEdge
      (printedGeneratedInitialSiblingErasure T)
      (printedGeneratedInitialSiblingLeafEquiv T
        (printedGeneratedInitialFirstDescendantLeaf v)))) r

theorem printedGeneratedInitialSiblingSelectedOrigin_level
    {J : ℕ} (T : FiniteTerminalGenealogy J) (p r : Paper.Overlap)
    (v : FiniteCascadeRecordVertex T) :
    nativeStreamingOriginLevel (anisotropicBinaryObservationSchedule p)
      (printedGeneratedInitialSiblingSelectedOrigin T p r v) = r := by
  classical
  unfold printedGeneratedInitialSiblingSelectedOrigin
  split_ifs with hr hp
  · rfl
  · change anisotropicBinaryObservationSchedule p (printedGeneratedInitialSiblingVertexErase v).depth = r
    rw [printedGeneratedInitialSiblingVertexErase_depth]
    exact hp.symm
  · rfl

theorem printedGeneratedInitialSiblingSelectedOrigin_closed_cell
    {J : ℕ} (T : FiniteTerminalGenealogy J) (p r : Paper.Overlap)
    (v : FiniteCascadeRecordVertex T) :
    match printedGeneratedInitialSiblingSelectedOrigin T p r v with
    | .vertex w => anisotropicBinaryObservationSchedule p w.depth = r
    | .edge e l => l = r ∧ anisotropicBinaryObservationSchedule p (e.depth + 1) ≤ r ∧
        r ≤ anisotropicBinaryObservationSchedule p e.depth := by
  classical
  unfold printedGeneratedInitialSiblingSelectedOrigin
  by_cases hr : r < p
  · simp only [if_pos hr]
    exact ⟨trivial, r.property.1, hr.le⟩
  · simp only [if_neg hr]
    by_cases hp : r = p
    · simp only [if_pos hp]
      change anisotropicBinaryObservationSchedule p (printedGeneratedInitialSiblingVertexErase v).depth = r
      rw [printedGeneratedInitialSiblingVertexErase_depth]
      exact hp.symm
    · simp only [if_neg hp]
      refine ⟨trivial, ?_, ?_⟩
      · change anisotropicBinaryObservationSchedule p
          ((printedGeneratedSiblingLeafEdge _ _).depth + 1) ≤ r
        rw [printedGeneratedSiblingLeafEdge_depth]
        exact le_of_not_gt hr
      · change r ≤ anisotropicBinaryObservationSchedule p
          (printedGeneratedSiblingLeafEdge _ _).depth
        rw [printedGeneratedSiblingLeafEdge_depth]
        exact r.property.2

theorem printedGeneratedInitialSelectedRoot_above_fork_has_no_forks
    {J : ℕ} (T : FiniteTerminalGenealogy J) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (p : Paper.Overlap)
    (hfork : printedGeneratedInitialForksAt q p T) (hr : p < q J) :
    printedGeneratedInitialSiblingErasure T = .single := by
  by_contra hno
  obtain ⟨j, hj, hp⟩ := printedGeneratedInitialSiblingErasure_has_fork T q p hfork hno
  exact (not_le_of_gt hr) ((hq hj).trans_eq hp)

theorem printedGeneratedInitialSelectedFork_child_level
    {J : ℕ} {T U : FiniteTerminalGenealogy J}
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (p : Paper.Overlap)
    (hfork : printedGeneratedInitialForksAt q p (.fork T U))
    (v : FiniteCascadeRecordVertex T) : p ≤ q v.depth := by
  rw [←hfork.1]
  exact hq v.depth_le

theorem printedGeneratedInitialSelectedFork_child_at_low_level
    {J : ℕ} {T U : FiniteTerminalGenealogy J}
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (p : Paper.Overlap)
    (hfork : printedGeneratedInitialForksAt q p (.fork T U))
    (v : FiniteCascadeRecordVertex T) (hr : q v.depth ≤ p) : q v.depth = p :=
  le_antisymm hr (printedGeneratedInitialSelectedFork_child_level q hq p hfork v)

end QuantitativeFollowup
