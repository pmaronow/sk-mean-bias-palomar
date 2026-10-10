module
public import QuantitativeFollowup.FollowupCavityGeneratedForestRefinement

@[expose] public section

/-! A genuine constructed forest survives mark reindexing, including
repeated coordinates. Its endpoint labels stay fixed. Compatible
histories give exactly the same clocks and full native record laws. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m M n : ℕ}

def CavityGeneratedConstructedForest.reindex
    (W : CavityGeneratedConstructedForest m) (τ : Fin m→Fin M) :
    CavityGeneratedConstructedForest M where
  componentCount := W.componentCount
  depth := W.depth
  tree := W.tree
  label := fun c j=>(W.label c j).reindex τ
  terminal_label := by
    intro c
    rw [W.terminal_label]
    rfl
  initial_label := by
    intro c
    rw [W.initial_label]
    rfl
  construction := by
    intro c
    apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
    intro b e hbe
    have hj := cavityGenerated_observationCommonLevel_le (W.tree c) b e
    obtain ⟨i,hi⟩ := (W.construction c).pair_clock_labels b e hbe
    have hi' : W.label c ⟨observationCommonLevel (W.tree c) b e,by omega⟩=.mark i := by
      simpa only [cavityGeneratedFiniteClockLabels,dif_pos hj] using hi
    refine ⟨τ i,?_⟩
    simp only [cavityGeneratedFiniteClockLabels,dif_pos hj]
    rw [hi']
    rfl

theorem CavityGeneratedConstructedForest.reindex_rawClock
    (W : CavityGeneratedConstructedForest m) (τ : Fin m→Fin M)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i,H (τ i)=h i)
    (c : Fin W.componentCount) (j : ℕ) :
    (W.reindex τ).clockTemplate.rawClock H c j=W.clockTemplate.rawClock h c j := by
  by_cases hj : j≤W.depth c
  · simp only [CavityGeneratedForestClockTemplate.rawClock,CavityGeneratedConstructedForest.reindex,
      CavityGeneratedConstructedForest.clockTemplate,dif_pos hj]
    exact CavityGeneratedClockLabel.reindex_value τ _ h H he
  · simp only [CavityGeneratedForestClockTemplate.rawClock,CavityGeneratedConstructedForest.reindex,
      CavityGeneratedConstructedForest.clockTemplate,dif_neg hj]

theorem CavityGeneratedConstructedForest.reindex_clock
    (W : CavityGeneratedConstructedForest m) (τ : Fin m→Fin M)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i,H (τ i)=h i)
    (c : Fin W.componentCount) :
    (W.reindex τ).clockTemplate.clock H c=W.clockTemplate.clock h c := by
  exact congrArg cavityGeneratedClippedClock
    (funext fun j=>W.reindex_rawClock τ h H he c j)

theorem CavityGeneratedConstructedForest.reindex_orderSet
    (W : CavityGeneratedConstructedForest m) (τ : Fin m→Fin M) :
    (W.reindex τ).clockTemplate.orderSet=
      (fun H : CavityGeneratedHistory Paper.Overlap M=>H ∘ τ) ⁻¹' W.clockTemplate.orderSet := by
  ext H
  change (∀c,∀j : Fin (W.depth c),
      (W.reindex τ).clockTemplate.rawClock H c (j+1)≤
        (W.reindex τ).clockTemplate.rawClock H c j) ↔
    (∀c,∀j : Fin (W.depth c),
      W.clockTemplate.rawClock (H ∘ τ) c (j+1)≤W.clockTemplate.rawClock (H ∘ τ) c j)
  simp only [W.reindex_rawClock τ (H ∘ τ) H (fun _=>rfl)]

theorem CavityGeneratedConstructedForest.reindex_record_law
    (W : CavityGeneratedConstructedForest m) (τ : Fin m→Fin M)
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i,H (τ i)=h i)
    (c : Fin W.componentCount) :
    anisotropicRecordedProfileTreeLaw D μ a ((W.reindex τ).clockTemplate.clock H c)
        ((W.reindex τ).tree c)=
      anisotropicRecordedProfileTreeLaw D μ a (W.clockTemplate.clock h c) (W.tree c) := by
  rw [W.reindex_clock τ h H he c]
  rfl

end QuantitativeFollowup
