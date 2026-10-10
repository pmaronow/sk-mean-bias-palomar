module
public import QuantitativeFollowup.FollowupCavityGeneratedForestConstruction
public import FourPapersCommon.FiniteObservationRefinementLeafGeometry

@[expose] public section

/-! Unary observation insertion and history-coordinate reindexing preserve
actual constructed genealogies. No new branch is created by padding; a
fork keeps its original mark at the literal refined depth. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def CavityGeneratedClockLabel.reindex {m M : ℕ} (τ : Fin m → Fin M) :
    CavityGeneratedClockLabel m → CavityGeneratedClockLabel M
  | .terminal => .terminal
  | .initial => .initial
  | .mark i => .mark (τ i)

theorem CavityGeneratedClockLabel.reindex_value {m M : ℕ}
    (τ : Fin m → Fin M) (l : CavityGeneratedClockLabel m)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i, H (τ i) = h i) :
    (l.reindex τ).value H = l.value h := by
  cases l with
  | terminal => rfl
  | initial => rfl
  | mark i => exact he i

theorem CavityGeneratedGenealogyConstruction.of_pair_clock_labels {m j : ℕ}
    {labels : ℕ → CavityGeneratedClockLabel m} (T : FiniteTerminalGenealogy j)
    (hT : cavityGeneratedPairClockLabels T labels) :
    CavityGeneratedGenealogyConstruction labels T := by
  induction T with
  | leaf => exact .linear 0
  | advance T ih => exact .advance (ih hT)
  | @fork j T U ihT ihU =>
      obtain ⟨i, hi⟩ := hT (Sum.inl (cavityGeneratedChosenLeaf T))
        (Sum.inr (cavityGeneratedChosenLeaf U)) (by intro he; cases he)
      apply CavityGeneratedGenealogyConstruction.fork i hi
      · apply ihT
        intro b e hbe
        exact hT (Sum.inl b) (Sum.inl e) (fun he => hbe (Sum.inl.inj he))
      · apply ihU
        intro b e hbe
        exact hT (Sum.inr b) (Sum.inr e) (fun he => hbe (Sum.inr.inj he))

theorem CavityGeneratedGenealogyConstruction.pad {m j : ℕ}
    {labels : ℕ → CavityGeneratedClockLabel m} {T : FiniteTerminalGenealogy j}
    (hT : CavityGeneratedGenealogyConstruction labels T) (d : ℕ) :
    CavityGeneratedGenealogyConstruction labels (observationTreePad T d) := by
  induction d with
  | zero => exact hT
  | succ d ih => exact .advance ih

theorem cavityGeneratedPairClockLabels_refinement {m M j : ℕ}
    (τ : Fin m → Fin M) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy j)
    (labels : ℕ → CavityGeneratedClockLabel m)
    (refined : ℕ → CavityGeneratedClockLabel M)
    (hT : cavityGeneratedPairClockLabels T labels)
    (hclock : ∀p, p ≤ j → refined (observationRefinementDepth d p) =
      (labels p).reindex τ) :
    cavityGeneratedPairClockLabels (observationRefineTree d T) refined := by
  induction T with
  | leaf => exact cavityGenerated_linear_clock_labels 0 refined
  | @advance j T ih =>
      have hc : ∀p, p ≤ j → refined (observationRefinementDepth d p) =
          (labels p).reindex τ := fun p hp => hclock p (by omega)
      have ht := CavityGeneratedGenealogyConstruction.of_pair_clock_labels _ (ih hT hc)
      exact (CavityGeneratedGenealogyConstruction.advance (ht.pad (d j))).pair_clock_labels
  | @fork j T U ihT ihU =>
      obtain ⟨i,hi⟩ := hT (Sum.inl (cavityGeneratedChosenLeaf T))
        (Sum.inr (cavityGeneratedChosenLeaf U)) (by intro he; cases he)
      apply cavityGenerated_fork_clock_labels
      · apply ihT _ hclock
        intro b e hbe
        exact hT (Sum.inl b) (Sum.inl e) (fun he => hbe (Sum.inl.inj he))
      · apply ihU _ hclock
        intro b e hbe
        exact hT (Sum.inr b) (Sum.inr e) (fun he => hbe (Sum.inr.inj he))
      · refine ⟨τ i, ?_⟩
        change labels j = .mark i at hi
        rw [hclock j le_rfl, hi]
        rfl

theorem CavityGeneratedGenealogyConstruction.refinement {m M j : ℕ}
    (τ : Fin m → Fin M) (d : ℕ → ℕ) {T : FiniteTerminalGenealogy j}
    {labels : ℕ → CavityGeneratedClockLabel m}
    (refined : ℕ → CavityGeneratedClockLabel M)
    (hT : CavityGeneratedGenealogyConstruction labels T)
    (hclock : ∀p, p ≤ j → refined (observationRefinementDepth d p) =
      (labels p).reindex τ) :
    CavityGeneratedGenealogyConstruction refined (observationRefineTree d T) :=
  .of_pair_clock_labels _ (cavityGeneratedPairClockLabels_refinement τ d T labels refined
    hT.pair_clock_labels hclock)

theorem cavityGeneratedRefined_pair_clock_value {m M j : ℕ}
    (τ : Fin m → Fin M) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy j)
    (labels : ℕ → CavityGeneratedClockLabel m)
    (refined : ℕ → CavityGeneratedClockLabel M)
    (hclock : ∀p, p ≤ j → refined (observationRefinementDepth d p) =
      (labels p).reindex τ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i, H (τ i) = h i)
    (b e : ObservationLeaf T) :
    (refined (observationCommonLevel (observationRefineTree d T)
      (observationRefinementLeafEmbed d T b) (observationRefinementLeafEmbed d T e))).value H =
      (labels (observationCommonLevel T b e)).value h := by
  rw [observationRefinementLeafEmbed_commonLevel,
    hclock _ (cavityGenerated_observationCommonLevel_le T b e)]
  exact CavityGeneratedClockLabel.reindex_value τ _ h H he

end QuantitativeFollowup
