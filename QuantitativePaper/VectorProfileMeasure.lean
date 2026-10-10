module
public import QuantitativePaper.VectorPosteriorMetric
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! Literal finite free overlap measures for the floor-root vector scheme.
The root atom is retained, and every feature weight is an actual Stieltjes
increment rather than a symbolic integration convention. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorProfileAtom {k : ℕ} (s : RSBScheme k)
    (i : vectorPosteriorFeatureIndex k) : Overlap :=
  ⟨s.q (vectorPosteriorFeatureTime i),s.q_nonneg (by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega),s.q_le_one (by
    cases i <;> dsimp [vectorPosteriorFeatureTime] <;> omega)⟩

def vectorProfileFreeMeasure {k : ℕ} (s : RSBScheme k) (a : ℝ) : Measure Overlap :=
  ∑ i,ENNReal.ofReal (vectorPosteriorFeatureWeight s a i) • Measure.dirac (vectorProfileAtom s i)

instance vectorProfileFreeMeasure_finite {k : ℕ} (s : RSBScheme k) (a : ℝ) :
    IsFiniteMeasure (vectorProfileFreeMeasure s a) := ⟨by
  classical
  simp [vectorProfileFreeMeasure,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,
    ENNReal.sum_lt_top]⟩

theorem vectorProfile_free_root_decomposition {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (h₀ : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) :
    ENNReal.ofReal a • Measure.dirac zeroOverlap+vectorProfileFreeMeasure s a=
      (Paper.parisiSchemeMeasure s : Measure Overlap) := by
  classical
  have hm : ENNReal.ofReal (s.m 1)=ENNReal.ofReal a+ENNReal.ofReal (s.m 1-a) := by
    rw [←ENNReal.ofReal_add h₀ (sub_nonneg.mpr ha)]
    congr 1
    ring
  have hz : Paper.parisiSchemeAtom s (0 : Fin (k+1))=zeroOverlap := by
    apply Subtype.ext
    exact hq
  have hf : vectorProfileAtom s none=zeroOverlap := by
    apply Subtype.ext
    exact hq
  change _=Paper.parisiSchemeRawMeasure s
  unfold vectorProfileFreeMeasure Paper.parisiSchemeRawMeasure
  rw [Fintype.sum_option,Fin.sum_univ_succ]
  simp only [vectorPosteriorFeatureWeight,vectorPosteriorFeatureTime,Fin.val_zero,
    zero_add,s.m_zero,sub_zero,hz,hf,hm,add_smul]
  rw [add_assoc]
  congr 2

theorem parisiSchemeMeasure_mem_scalarFloor {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (h₀ : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) :
    Paper.parisiSchemeMeasure s ∈ scalarFloor a := by
  change ENNReal.ofReal a ≤ _
  rw [←vectorProfile_free_root_decomposition s a h₀ ha hq,
    Measure.add_apply,Measure.smul_apply]
  simp only [Measure.dirac_apply_of_mem (mem_singleton _),smul_eq_mul,mul_one]
  exact le_add_right le_rfl

theorem vectorProfileFreeMeasure_eq_actual_free {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (h₀ : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) :
    vectorProfileFreeMeasure s a=
      QuantitativeFollowup.parisiFreeMeasure (Paper.parisiSchemeMeasure s) a := by
  have h₁ : a ≤ 1 := ha.trans (s.m_le_one (by omega))
  letI : IsFiniteMeasure (ENNReal.ofReal a • Measure.dirac zeroOverlap) := ⟨by
    simp only [Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
    exact ENNReal.ofReal_lt_top⟩
  rw [QuantitativeFollowup.parisiFreeMeasure_eq_sub _ _ ⟨h₀,h₁⟩
    (parisiSchemeMeasure_mem_scalarFloor s a h₀ ha hq),
    ←vectorProfile_free_root_decomposition s a h₀ ha hq,add_comm,Measure.add_sub_cancel]

theorem vectorProfileFreeMeasure_univ {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (h₀ : 0 ≤ a) (ha : a ≤ s.m 1) (hq : s.q 1=0) :
    vectorProfileFreeMeasure s a univ=ENNReal.ofReal (1-a) := by
  rw [vectorProfileFreeMeasure_eq_actual_free s a h₀ ha hq]
  exact QuantitativeFollowup.parisiFreeMeasure_univ _ _

theorem integrable_vectorProfileFreeMeasure {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (f : Overlap → ℝ) : Integrable f (vectorProfileFreeMeasure s a) := by
  classical
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem integral_vectorProfileFreeMeasure {k : ℕ} (s : RSBScheme k)
    (a : ℝ) (ha : a ≤ s.m 1) (f : Overlap → ℝ) :
    (∫q,f q ∂vectorProfileFreeMeasure s a)=
      ∑ i,vectorPosteriorFeatureWeight s a i*f (vectorProfileAtom s i) := by
  classical
  unfold vectorProfileFreeMeasure
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,
    ENNReal.toReal_ofReal (vectorPosteriorFeatureWeight_nonneg s a ha i)]
  rfl

end QuantitativePaper
