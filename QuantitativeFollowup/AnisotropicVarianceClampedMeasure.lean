module
public import QuantitativeFollowup.AnisotropicVarianceResponseFinite
public import FRSB.FiniteForwardAction

@[expose] public section

/-! The clamped finite profile is the genuine push-forward by max(q,·),
with the additional compulsory zero root carrying zero probability mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativeFollowup
open QuantitativePaper SpinGlass SpinGlass.Targets
variable {k : ℕ}
set_option maxHeartbeats 1400000

def anisotropicClampOverlap (q : Paper.Overlap) (r : Paper.Overlap) : Paper.Overlap :=
  ⟨max (q:ℝ) (r:ℝ),(q.property.1.trans (le_max_left _ _)),max_le q.property.2 r.property.2⟩

@[simp] theorem anisotropicClampOverlap_coe (q r : Paper.Overlap) :
    (anisotropicClampOverlap q r:ℝ)=max (q:ℝ) (r:ℝ) := rfl

theorem continuous_anisotropicClampOverlap (q : Paper.Overlap) : Continuous (anisotropicClampOverlap q) := by
  apply Continuous.subtype_mk
  exact continuous_const.max continuous_subtype_val

theorem integral_anisotropicClampedSchemeMeasure (s : RSBScheme k) (q : Paper.Overlap)
    (f : Paper.Overlap→ℝ) :
    (∫r,f r∂(Paper.parisiSchemeMeasure (vectorClampedScheme s q q.property):Measure Paper.Overlap))=
      ∫r,f (anisotropicClampOverlap q r)∂(Paper.parisiSchemeMeasure s:Measure Paper.Overlap) := by
  rw [FRSB.integral_parisiSchemeMeasure,FRSB.integral_parisiSchemeMeasure,Fin.sum_univ_succ]
  have hz : (vectorClampedScheme s q q.property).m 1-(vectorClampedScheme s q q.property).m 0=0 := by
    simp only [vectorClampedScheme_mass_succ,s.m_zero,(vectorClampedScheme s q q.property).m_zero,sub_self]
  simp only [Fin.val_zero,Nat.zero_add,hz,zero_mul,zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  have hatom : Paper.parisiSchemeAtom (vectorClampedScheme s q q.property) i.succ=
      anisotropicClampOverlap q (Paper.parisiSchemeAtom s i) := by
    apply Subtype.ext
    simp only [Paper.parisiSchemeAtom,Fin.val_succ,anisotropicClampOverlap_coe,
      vectorClampedScheme_overlap_succ]
  rw [hatom]
  congr 1

end QuantitativeFollowup
