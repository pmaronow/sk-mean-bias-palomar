module
public import QuantitativeFollowup.FollowupCavityGeneratedForestClocks
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry
public import FourPapersCommon.FiniteCascadeContinuationVertexGeometry

@[expose] public section

/-! Genuine continuation grafts preserve earlier branch labels. The
only new old/fresh split is the marked retained vertex; fresh/fresh
splits are the actual continuation's labels. These are structural
identities, independent of all measure and cubic estimates. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedChosenLeaf : {j : ℕ} → (T : FiniteTerminalGenealogy j) → ObservationLeaf T
  | _, .leaf => PUnit.unit
  | _, .advance T => cavityGeneratedChosenLeaf T
  | _, .fork T _ => Sum.inl (cavityGeneratedChosenLeaf T)

def cavityGeneratedPairClockLabels {m j : ℕ} (T : FiniteTerminalGenealogy j)
    (labels : ℕ → CavityGeneratedClockLabel m) : Prop :=
  ∀b e : ObservationLeaf T, b ≠ e → ∃i : Fin m,
    labels (observationCommonLevel T b e) = .mark i

theorem cavityGenerated_advance_clock_labels {m j : ℕ}
    (T : FiniteTerminalGenealogy j) (labels : ℕ → CavityGeneratedClockLabel m)
    (hT : cavityGeneratedPairClockLabels T labels) :
    cavityGeneratedPairClockLabels (.advance T) labels := hT

theorem cavityGenerated_fork_clock_labels {m j : ℕ}
    (T U : FiniteTerminalGenealogy j) (labels : ℕ → CavityGeneratedClockLabel m)
    (hT : cavityGeneratedPairClockLabels T labels)
    (hU : cavityGeneratedPairClockLabels U labels)
    (hj : ∃i : Fin m, labels j = .mark i) :
    cavityGeneratedPairClockLabels (.fork T U) labels := by
  intro b e hbe
  cases b with
  | inl b => cases e with
    | inl e => exact hT b e (fun he => hbe (congrArg Sum.inl he))
    | inr e => exact hj
  | inr b => cases e with
    | inl e => exact hj
    | inr e => exact hU b e (fun he => hbe (congrArg Sum.inr he))

theorem cavityGenerated_linear_clock_labels {m : ℕ}
    (d : ℕ) (labels : ℕ → CavityGeneratedClockLabel m) :
    cavityGeneratedPairClockLabels (finiteCascadeLinearTerminalTree d) labels := by
  induction d with
  | zero =>
      intro b e hbe
      exact (hbe (by cases b; cases e; rfl)).elim
  | succ d ih => exact ih

theorem cavityGenerated_observationCommonLevel_symm {j : ℕ}
    (T : FiniteTerminalGenealogy j) (b e : ObservationLeaf T) :
    observationCommonLevel T b e = observationCommonLevel T e b := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih b e
  | fork T U ihT ihU =>
      cases b with
      | inl b => cases e with
        | inl e => exact ihT b e
        | inr e => rfl
      | inr b => cases e with
        | inl e => rfl
        | inr e => exact ihU b e

theorem cavityGenerated_leaf_vertex_clock_label {m j : ℕ}
    {T : FiniteTerminalGenealogy j} (v : FiniteCascadeRecordVertex T) :
    ∀labels : ℕ → CavityGeneratedClockLabel m,
    cavityGeneratedPairClockLabels T labels →
    (∃i : Fin m, labels v.depth = .mark i) →
    ∀b : ObservationLeaf T, ∃i : Fin m,
      labels (finiteCascadeCommonPathDepth T (observationLeafVertex T b) v) = .mark i := by
  induction v with
  | root T =>
      intro labels hpair hv b
      rw [finiteCascadeCommonPathDepth_root_right]
      exact hv
  | child v ih =>
      intro labels hpair hv b
      exact ih labels hpair hv b
  | @left j T U v ih =>
      intro labels hpair hv b
      cases b with
      | inl b =>
          apply ih labels _ hv b
          intro x y hxy
          exact hpair (Sum.inl x) (Sum.inl y)
            (fun he => hxy (Sum.inl.inj he))
      | inr b =>
          exact hpair (Sum.inl (cavityGeneratedChosenLeaf T)) (Sum.inr b)
            (by intro he; cases he)
  | @right j T U v ih =>
      intro labels hpair hv b
      cases b with
      | inl b =>
          exact hpair (Sum.inl b) (Sum.inr (cavityGeneratedChosenLeaf U))
            (by intro he; cases he)
      | inr b =>
          apply ih labels _ hv b
          intro x y hxy
          exact hpair (Sum.inr x) (Sum.inr y)
            (fun he => hxy (Sum.inr.inj he))

theorem cavityGenerated_continuation_graft_clock_labels {m j : ℕ}
    (U : (d : ℕ) → FiniteTerminalGenealogy d) {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (labels : ℕ → CavityGeneratedClockLabel m)
    (hOld : cavityGeneratedPairClockLabels T labels)
    (hVertex : ∃i : Fin m, labels v.depth = .mark i)
    (hNew : cavityGeneratedPairClockLabels (U v.depth) labels) :
    cavityGeneratedPairClockLabels (finiteCascadeContinuationGraft U v) labels := by
  intro b e hbe
  rcases finiteCascadeContinuationLeaf_partition U v b with ⟨b, rfl⟩ | ⟨b, rfl⟩
  · rcases finiteCascadeContinuationLeaf_partition U v e with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · rw [finiteCascadeContinuationOldLeaf_commonLevel]
      exact hOld b e (fun he => hbe (congrArg (finiteCascadeContinuationOldLeaf U v) he))
    · rw [finiteCascadeContinuationOldNewLeaf_commonLevel]
      exact cavityGenerated_leaf_vertex_clock_label v labels hOld hVertex b
  · rcases finiteCascadeContinuationLeaf_partition U v e with ⟨e, rfl⟩ | ⟨e, rfl⟩
    · rw [cavityGenerated_observationCommonLevel_symm,
        finiteCascadeContinuationOldNewLeaf_commonLevel]
      exact cavityGenerated_leaf_vertex_clock_label v labels hOld hVertex e
    · rw [finiteCascadeContinuationNewLeaf_commonLevel]
      exact hNew b e (fun he => hbe (congrArg (finiteCascadeContinuationNewLeaf U v) he))

theorem cavityGenerated_continuation_vertex_keeps_clock_label {m j : ℕ}
    (U : (d : ℕ) → FiniteTerminalGenealogy d) {T : FiniteTerminalGenealogy j}
    (v w : FiniteCascadeRecordVertex T) (labels : ℕ → CavityGeneratedClockLabel m) :
    labels (finiteCascadeContinuationVertexEmbed U v w).depth = labels w.depth := by
  rw [finiteCascadeContinuationVertexEmbed_depth]

end QuantitativeFollowup
