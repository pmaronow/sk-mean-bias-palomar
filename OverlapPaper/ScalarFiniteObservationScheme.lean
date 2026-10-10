module
public import QuantitativeFollowup.ScalarObservationRefinement
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Arbitrary finite observation sets can be retained in a genuine finite
scheme without changing its probability law. All inserted masses are zero;
the existing atoms and their multiplicities are preserved exactly. -/
noncomputable section
open Set MeasureTheory
open scoped Classical
namespace OverlapPaper
open Paper SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1200000

theorem scalarObservationRefinement_preserves_node {k : ℕ} (s : RSBScheme k)
    (p : Overlap) (i : Fin (k+3)) :
    scalarSchemeTransportNode (scalarObservationRefinement s p) (3*(i:ℕ)) =
      scalarSchemeTransportNode s i := by
  apply Subtype.ext
  rw [scalarSchemeTransportNode_coe _ _ (by have := i.isLt; omega),
    scalarSchemeTransportNode_coe _ _ (by have := i.isLt; omega)]
  exact FourPapersCommon.threefoldScheme_q_original s _ _ _ i

theorem exists_scalar_same_measure_scheme_observations {k : ℕ} (s : RSBScheme k)
    (E : Finset Overlap) :
    ∃ (K : ℕ) (r : RSBScheme K), parisiSchemeMeasure r = parisiSchemeMeasure s ∧
      ∀ p ∈ E, ∃ j : Fin (K+3), scalarSchemeTransportNode r j = p := by
  induction E using Finset.induction_on with
  | empty => exact ⟨k,s,rfl,by simp⟩
  | @insert p E hp ih =>
    obtain ⟨K,r,hr,hE⟩ := ih
    refine ⟨3*K+4,scalarObservationRefinement r p,
      (scalarObservationRefinement_measure r p).trans hr,?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with hqp | hqE
    · subst q
      exact exists_scalarObservationRefinement_node r p
    · obtain ⟨j,hj⟩ := hE q hqE
      refine ⟨⟨3*(j:ℕ),by have := j.isLt; omega⟩,?_⟩
      exact (scalarObservationRefinement_preserves_node r p j).trans hj

theorem exists_finiteLaw_scheme_observations (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (E : Finset Overlap) :
    ∃ (K : ℕ) (r : RSBScheme K), parisiSchemeMeasure r = μ ∧
      ∀ p ∈ E, ∃ j : Fin (K+3), scalarSchemeTransportNode r j = p := by
  obtain ⟨K,r,hr,hE⟩ := exists_scalar_same_measure_scheme_observations
    (FRSB.finiteLawRSBScheme μ hμ) E
  exact ⟨K,r,hr.trans (FRSB.parisiSchemeMeasure_finiteLawRSBScheme μ hμ),hE⟩

theorem exists_finiteLaw_scheme_observation_family {ι : Type*} [Fintype ι]
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite) (T : ι → Overlap) :
    ∃ (K : ℕ) (r : RSBScheme K) (j : ι → Fin (K+3)),
      parisiSchemeMeasure r = μ ∧ ∀ i, scalarSchemeTransportNode r (j i) = T i := by
  obtain ⟨K,r,hr,hT⟩ := exists_finiteLaw_scheme_observations μ hμ (Finset.univ.image T)
  choose j hj using fun i => hT (T i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  exact ⟨K,r,j,hr,hj⟩

end OverlapPaper
