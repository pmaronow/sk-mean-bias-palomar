module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkClockConsistency

@[expose] public section

/-! An actual atom-weighted vertex attachment appends its physical clock,
retains the old tree, and constructs the genuine one- or two-descendant
graft. Clock consistency is derived from the atom law. Endpoint slots are
kept as repeated observations before this interior attachment operation. -/
noncomputable section
open MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m j : ℕ}

def cavityGeneratedAttachedClockLabels (labels : ℕ → CavityGeneratedClockLabel m)
    (d : ℕ) (p : ℕ) : CavityGeneratedClockLabel (m+1) :=
  if p = d then .mark (Fin.last m) else (labels p).reindex Fin.castSucc

theorem cavityGeneratedAttachedClockLabels_at_depth
    (labels : ℕ → CavityGeneratedClockLabel m) (d : ℕ) :
    cavityGeneratedAttachedClockLabels labels d d = .mark (Fin.last m) := by
  simp [cavityGeneratedAttachedClockLabels]

def cavityGeneratedVertexAtomProgram
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (labels : ℕ → CavityGeneratedClockLabel m) (d : ℕ) :
    CavityGeneratedMarkProgram Paper.Overlap (m+1) :=
  .atom P (labels d).value (labels d).continuous_value.measurable

theorem cavityGeneratedVertexAtomProgram_budget
    (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (labels : ℕ → CavityGeneratedClockLabel m) (d : ℕ) :
    (cavityGeneratedVertexAtomProgram P labels d).budget = P.budget := rfl

theorem cavityGeneratedAttachedClockLabels_consistent
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (labels : ℕ → CavityGeneratedClockLabel m) (d : ℕ) :
    ∀ᵐ H ∂(cavityGeneratedVertexAtomProgram P labels d).measure ν, ∀p,
      (cavityGeneratedAttachedClockLabels labels d p).value H =
        (labels p).value (cavityGeneratedHistoryPrefix H) := by
  have he := cavityGeneratedAtom_consistent ν P (labels d).value
    (labels d).continuous_value.measurable
  exact he.mono fun H hh p => by
    by_cases hp : p = d
    · subst p
      rw [cavityGeneratedAttachedClockLabels_at_depth]
      exact hh
    · rw [cavityGeneratedAttachedClockLabels, if_neg hp,
        CavityGeneratedClockLabel.append_reindex_value]

theorem cavityGeneratedVertexAtom_preserves_old_record_law
    {n : ℕ} (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (labels : ℕ → CavityGeneratedClockLabel m) (T : FiniteTerminalGenealogy j) (d : ℕ) :
    ∀ᵐ H ∂(cavityGeneratedVertexAtomProgram P labels d).measure ν,
      anisotropicRecordedProfileTreeLaw D μ a
          (fun p => (cavityGeneratedAttachedClockLabels labels d p).value H) T =
        anisotropicRecordedProfileTreeLaw D μ a
          (fun p => (labels p).value (cavityGeneratedHistoryPrefix H)) T := by
  exact (cavityGeneratedAttachedClockLabels_consistent ν P labels d).mono fun H hh => by
    have he : (fun p => (cavityGeneratedAttachedClockLabels labels d p).value H) =
        (fun p => (labels p).value (cavityGeneratedHistoryPrefix H)) := funext hh
    rw [he]

theorem cavityGeneratedBranchAttachedClockLabels_consistent
    (μ : Paper.ParisiMeasure) (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (labels : ℕ → CavityGeneratedClockLabel m) (d : ℕ) (i : Fin m)
    (hi : labels d = .mark i) (l : ℕ) :
    ∀ᵐ H ∂(cavityGeneratedBranchMarkProgram μ P i l).measure (parisiFreeMeasure μ a), ∀p,
      (cavityGeneratedAttachedClockLabels labels d p).value H =
        (labels p).value (cavityGeneratedHistoryPrefix H) := by
  have he := cavityGeneratedBranch_consistent μ a P i l
  exact he.mono fun H hh p => by
    by_cases hp : p = d
    · subst p
      rw [cavityGeneratedAttachedClockLabels_at_depth, hi]
      exact hh
    · rw [cavityGeneratedAttachedClockLabels, if_neg hp,
        CavityGeneratedClockLabel.append_reindex_value]

theorem CavityGeneratedGenealogyConstruction.attached_clock_relabel
    {labels : ℕ → CavityGeneratedClockLabel m} {T : FiniteTerminalGenealogy j}
    (hT : CavityGeneratedGenealogyConstruction labels T) (d : ℕ) :
    CavityGeneratedGenealogyConstruction (cavityGeneratedAttachedClockLabels labels d) T := by
  apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
  intro b e hbe
  by_cases hd : observationCommonLevel T b e = d
  · exact ⟨Fin.last m, by rw [hd]; exact cavityGeneratedAttachedClockLabels_at_depth labels d⟩
  · obtain ⟨i,hi⟩ := hT.pair_clock_labels b e hbe
    refine ⟨i.castSucc, ?_⟩
    rw [cavityGeneratedAttachedClockLabels, if_neg hd, hi]
    rfl

theorem CavityGeneratedGenealogyConstruction.atom_single_graft
    {labels : ℕ → CavityGeneratedClockLabel m} {T : FiniteTerminalGenealogy j}
    (hT : CavityGeneratedGenealogyConstruction labels T) (v : FiniteCascadeRecordVertex T) :
    CavityGeneratedGenealogyConstruction (cavityGeneratedAttachedClockLabels labels v.depth)
      (finiteCascadeContinuationGraft finiteCascadeLinearTerminalTree v) := by
  apply CavityGeneratedGenealogyConstruction.graft finiteCascadeLinearTerminalTree v (Fin.last m)
  · exact cavityGeneratedAttachedClockLabels_at_depth labels v.depth
  · exact hT.attached_clock_relabel v.depth
  · exact .linear v.depth

theorem CavityGeneratedGenealogyConstruction.atom_current_pair_graft
    {labels : ℕ → CavityGeneratedClockLabel m} {T : FiniteTerminalGenealogy j}
    (hT : CavityGeneratedGenealogyConstruction labels T) (v : FiniteCascadeRecordVertex T) :
    CavityGeneratedGenealogyConstruction (cavityGeneratedAttachedClockLabels labels v.depth)
      (finiteCascadeContinuationGraft
        (fun d => .fork (finiteCascadeLinearTerminalTree d) (finiteCascadeLinearTerminalTree d)) v) := by
  apply CavityGeneratedGenealogyConstruction.graft _ v (Fin.last m)
  · exact cavityGeneratedAttachedClockLabels_at_depth labels v.depth
  · exact hT.attached_clock_relabel v.depth
  · apply CavityGeneratedGenealogyConstruction.fork (Fin.last m)
    · exact cavityGeneratedAttachedClockLabels_at_depth labels v.depth
    · exact .linear v.depth
    · exact .linear v.depth

end QuantitativeFollowup
