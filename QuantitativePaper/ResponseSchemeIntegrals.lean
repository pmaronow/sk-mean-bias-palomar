module
public import Paper.ParisiSchemeMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Literal integration against an actual finite scheme law, with every
atom coefficient retained and no integrability premise. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace QuantitativePaper
open SpinGlass.Targets
set_option maxHeartbeats 1800000
variable {k : ℕ}

theorem response_integral_scheme (s : RSBScheme k) (f : Paper.Overlap→ℝ) :
    (∫q,f q ∂(Paper.parisiSchemeMeasure s : Measure Paper.Overlap))=
      ∑i : Fin (k+1),(s.m (i+1)-s.m i)*f (Paper.parisiSchemeAtom s i) := by
  change (∫q,f q ∂Paper.parisiSchemeRawMeasure s)=_
  unfold Paper.parisiSchemeRawMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal]
    · rfl
    · exact sub_nonneg.mpr (s.m_mono i (by omega))
  · intro i _
    exact (integrable_dirac (by simp)).smul_measure (by simp)

end QuantitativePaper
