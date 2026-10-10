module
public import QuantitativeFollowup.ScalarResponseRootCancellation
public import QuantitativeFollowup.ScalarTransportScoreContraction
public import FRSB.FiniteForwardAction

@[expose] public section

/-! The literal scalar response is the exact retained-node sum for a finite
scheme, even when the prescribed root mass is smaller than the actual atom. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal BigOperators
namespace QuantitativeFollowup
open Paper SpinGlass.Targets FourPapersCommon QuantitativePaper FRSB
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {k : ℕ}

theorem integral_scalarScheme_nodes (s : RSBScheme k) (f : Paper.Overlap→ℝ) :
    (∫r,f r ∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap))=
      ∑i : Fin (k+1),(s.m (i+1)-s.m i)*f (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)) := by
  rw [FRSB.integral_parisiSchemeMeasure]
  apply Finset.sum_congr rfl
  intro i _
  have he : Paper.parisiSchemeAtom s i=scalarSchemeTransportNode s (scalarFiniteAtomIndex i) := by
    apply Subtype.ext
    exact (scalarSchemeTransportNode_coe s (i+1) (by omega)).symm
  rw [he]

def scalarFiniteResponseSum (s : RSBScheme k) (β : ℝ) (φ : C(Paper.Overlap,ℝ))
    (p : Paper.Overlap) : ℝ :=
  β^2*(scalarResponseKernel0 β (Paper.parisiSchemeMeasure s) p 0 0*φ p+
    (∑i : Fin (k+1),(s.m (i+1)-s.m i)*scalarResponsePsi1 β (Paper.parisiSchemeMeasure s) φ p
      (scalarSchemeTransportNode s (scalarFiniteAtomIndex i)))+
    (∑i : Fin (k+1),(s.m (i+1)-s.m i)*(∑j : Fin (k+1),(s.m (j+1)-s.m j)*
      scalarResponsePsi2 β (Paper.parisiSchemeMeasure s) φ p
        (scalarSchemeTransportNode s (scalarFiniteAtomIndex i))
        (scalarSchemeTransportNode s (scalarFiniteAtomIndex j)))))

theorem scalarResponseOperator_eq_finite_sum (s : RSBScheme k) (β : ℝ) (hβ : β≠0)
    (rootMass : ℝ) (hs : rootMass∈Icc (0:ℝ) 1)
    (hμ : Paper.parisiSchemeMeasure s∈scalarFloor rootMass)
    (φ : C(Paper.Overlap,ℝ)) (h0 : φ 0=0) (p : Paper.Overlap) :
    scalarResponseOperator β hβ (Paper.parisiSchemeMeasure s) rootMass φ p=
      scalarFiniteResponseSum s β φ p := by
  rw [scalarResponseOperator_eq_full_regrouped β hβ (Paper.parisiSchemeMeasure s)
    rootMass hs hμ φ h0 p]
  simp_rw [integral_scalarScheme_nodes s]
  rfl

end QuantitativeFollowup
