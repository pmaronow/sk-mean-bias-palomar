module
public import HexagonPaper.VariableScalarClockPrimitiveDensityBasic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

/-! Genuine change of variables for a bounded positive measurable
coefficient clock, at the level of measures. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HexagonPaper

def scalarCoefficientRealClock (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) (x : ℝ) : ℝ :=
  scalarCoefficientClock c hint hpos (projIcc 0 1 zero_le_one x)

theorem continuous_scalarCoefficientRealClock (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    Continuous (scalarCoefficientRealClock c hint hpos) :=
  continuous_subtype_val.comp ((scalarCoefficientClock c hint hpos).continuous.comp
    continuous_projIcc)

theorem scalarCoefficientClockDensity_congr_inter (c : ℝ → ℝ)
    (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (heq : A ∩ Icc (0 : ℝ) 1 = B ∩ Icc 0 1) :
    scalarCoefficientClockDensity c A = scalarCoefficientClockDensity c B := by
  unfold scalarCoefficientClockDensity
  rw [withDensity_apply _ hA, withDensity_apply _ hB,
    Measure.restrict_restrict hA, Measure.restrict_restrict hB, heq]

theorem scalarCoefficientClockDensity_map (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 < c q) :
    (scalarCoefficientClockDensity c).map
      (scalarCoefficientRealClock c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩)) =
        volume.restrict (Icc (0 : ℝ) 1) := by
  let hp : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q := fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩
  let τ := scalarCoefficientClock c hint hp
  let f := scalarCoefficientRealClock c hint hp
  have hf : Measurable f := (continuous_scalarCoefficientRealClock c hint hp).measurable
  have hrange : ∀ x : ℝ, f x ∈ Icc (0 : ℝ) 1 := fun x => (τ (projIcc 0 1 zero_le_one x)).property
  haveI : IsProbabilityMeasure (scalarCoefficientClockDensity c) :=
    scalarCoefficientClockDensity_probability c hint hpos
  change (scalarCoefficientClockDensity c).map f = _
  apply Measure.ext_of_Iic
  intro y
  rw [Measure.map_apply hf measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  by_cases hy0 : y < 0
  · have hpre : f ⁻¹' Iic y = ∅ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
      exact not_le.mpr (hy0.trans_le (hrange x).1)
    have hset : Iic y ∩ Icc (0 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false, iff_false]
      intro hx
      linarith [hx.1, hx.2.1]
    rw [hpre, hset]
    simp
  by_cases hy1 : 1 ≤ y
  · have hpre : f ⁻¹' Iic y = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact (hrange x).2.trans hy1
    have hset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · exact And.right
      · intro hx
        exact ⟨hx.2.trans hy1, hx⟩
    rw [hpre, hset, measure_univ]
    simp
  let t : Paper.Overlap := ⟨y, le_of_not_gt hy0, le_of_not_ge hy1⟩
  let q : Paper.Overlap := τ.symm t
  have hset : f ⁻¹' Iic y ∩ Icc (0 : ℝ) 1 = Iic (q : ℝ) ∩ Icc 0 1 := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    by_cases hx : x ∈ Icc (0 : ℝ) 1
    · have hfval : f x = (τ ⟨x, hx⟩ : ℝ) := by
        dsimp only [f, scalarCoefficientRealClock]
        rw [projIcc_of_mem zero_le_one hx]
      rw [hfval]
      have heq : (τ ⟨x, hx⟩ : ℝ) ≤ y ↔ x ≤ (q : ℝ) := by
        change τ ⟨x, hx⟩ ≤ t ↔ (⟨x, hx⟩ : Paper.Overlap) ≤ q
        rw [← τ.apply_symm_apply t]
        exact τ.le_iff_le
      simp only [hx, and_true, heq]
    · simp only [hx, and_false]
  rw [scalarCoefficientClockDensity_congr_inter c _ _ (measurableSet_Iic.preimage hf)
    measurableSet_Iic hset, scalarCoefficientClockDensity_Iic c hint hpos q q.property]
  have hy : scalarCoefficientPrimitive c q / scalarCoefficientPrimitive c 1 = y := by
    change (∫ r in (0 : ℝ)..(q : ℝ), c r) / (∫ r in (0 : ℝ)..1, c r) = y
    rw [← scalarCoefficientClock_apply c hint hp q]
    exact congrArg Subtype.val (τ.apply_symm_apply t)
  rw [hy]
  have hI : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hxy, hx0, hx1⟩
      exact ⟨hx0, hxy⟩
    · rintro ⟨hx0, hxy⟩
      exact ⟨hxy, hx0, hxy.trans t.property.2⟩
  rw [hI]
  simp

end HexagonPaper
