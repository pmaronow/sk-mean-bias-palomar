module
public import QuantitativeFollowup.ScalarGaussianHistoryCurve
public import FourPapersCommon.ThreefoldSchemeRefinement
public import Paper.ParisiFiniteCells

@[expose] public section

/-! Every observation level is a retained node of a genuine same-measure
refinement. Inserted masses are exactly zero, even at repeated levels. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 600000
variable {k : ℕ}

def scalarObservationInsertedLevel (s : RSBScheme k) (p : Paper.Overlap) (i : ℕ) : ℝ :=
  max (s.q i) (min (p:ℝ) (s.q (i+1)))

theorem scalarObservationInsertedLevel_bounds (s : RSBScheme k) (p : Paper.Overlap)
    (i : ℕ) (hi : i ≤ k+1) :
    s.q i ≤ scalarObservationInsertedLevel s p i ∧
      scalarObservationInsertedLevel s p i ≤ s.q (i+1) := by
  refine ⟨le_max_left _ _,max_le ?_ (min_le_right _ _)⟩
  exact s.q_mono i (by omega)

def scalarObservationRefinement (s : RSBScheme k) (p : Paper.Overlap) : RSBScheme (3*k+4) :=
  threefoldScheme s (scalarObservationInsertedLevel s p) (scalarObservationInsertedLevel s p)
    (fun i hi=>⟨(scalarObservationInsertedLevel_bounds s p i hi).1,le_rfl,
      (scalarObservationInsertedLevel_bounds s p i hi).2⟩)

theorem scalarObservationRefinement_measure (s : RSBScheme k) (p : Paper.Overlap) :
    Paper.parisiSchemeMeasure (scalarObservationRefinement s p)=Paper.parisiSchemeMeasure s :=
  parisiSchemeMeasure_threefold s _ _ _

theorem exists_scalarObservationRefinement_node (s : RSBScheme k) (p : Paper.Overlap) :
    ∃j : Fin (3*k+7),scalarSchemeTransportNode (scalarObservationRefinement s p) j=p := by
  by_cases hp : (p:ℝ)<1
  · obtain ⟨i,hi,hcell,_⟩:=Paper.exists_parisiFinite_right_cell s ⟨p.property.1,hp⟩
    refine ⟨⟨3*i+1,by omega⟩,?_⟩
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe _ _ (by omega)]
    change (threefoldScheme s (scalarObservationInsertedLevel s p)
      (scalarObservationInsertedLevel s p) _).q (3*i+1)=(p:ℝ)
    rw [threefoldScheme_q_first]
    unfold scalarObservationInsertedLevel
    rw [min_eq_left hcell.2.le,max_eq_right hcell.1]
  · refine ⟨Fin.last (3*k+6),?_⟩
    apply Subtype.ext
    rw [scalarSchemeTransportNode_coe _ _ (by simp [Fin.val_last]),
      show (Fin.last (3*k+6):ℕ)=3*k+6 by rfl]
    rw [show 3*k+6=3*k+4+2 by omega,(scalarObservationRefinement s p).q_top]
    exact le_antisymm p.property.2 (le_of_not_gt hp) |>.symm

theorem exists_scalar_same_measure_scheme_node (s : RSBScheme k) (p : Paper.Overlap) :
    ∃(K : ℕ)(r : RSBScheme K)(j : Fin (K+3)),
      Paper.parisiSchemeMeasure r=Paper.parisiSchemeMeasure s ∧ scalarSchemeTransportNode r j=p := by
  obtain ⟨j,hj⟩:=exists_scalarObservationRefinement_node s p
  exact ⟨3*k+4,scalarObservationRefinement s p,j,scalarObservationRefinement_measure s p,hj⟩

end QuantitativeFollowup
