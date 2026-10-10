module
public import HexagonPaper.VariableScalarClockPrimitive
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! The coefficient-weighted clock measure, with its actual cumulative
mass. These identities retain endpoint atoms correctly (Lebesgue has none). -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace HexagonPaper

def scalarCoefficientClockDensity (c : ℝ → ℝ) : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 1)).withDensity
    (fun r => ENNReal.ofReal (c r / scalarCoefficientPrimitive c 1))

theorem scalarCoefficientClockDensity_Iic (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 < c q)
    (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
    scalarCoefficientClockDensity c (Iic q) =
      ENNReal.ofReal (scalarCoefficientPrimitive c q / scalarCoefficientPrimitive c 1) := by
  have htotal := scalarCoefficient_total_pos c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩)
  have hintq : IntervalIntegrable c volume 0 q := hint.mono_set (by
    rw [uIcc_of_le hq.1, uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    exact Icc_subset_Icc le_rfl hq.2)
  have hi : IntegrableOn c (Icc (0 : ℝ) q) volume :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hq.1).1 hintq
  have hset : Iic q ∩ Icc (0 : ℝ) 1 = Icc 0 q := by
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    constructor
    · rintro ⟨hrq, hr0, hr1⟩
      exact ⟨hr0, hrq⟩
    · rintro ⟨hr0, hrq⟩
      exact ⟨hrq, hr0, hrq.trans hq.2⟩
  unfold scalarCoefficientClockDensity
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic, hset,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const (scalarCoefficientPrimitive c 1))]
  · congr 1
    rw [integral_div, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hq.1]
    rfl
  · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all volume
      (fun r hr => div_nonneg (hpos r ⟨hr.1, hr.2.trans hq.2⟩).le htotal.le))

theorem scalarCoefficientClockDensity_univ (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 < c q) :
    scalarCoefficientClockDensity c univ = 1 := by
  have htotal := scalarCoefficient_total_pos c hint (fun r hr => hpos r ⟨hr.1.le, hr.2.le⟩)
  have heq : scalarCoefficientClockDensity c univ = scalarCoefficientClockDensity c (Iic 1) := by
    unfold scalarCoefficientClockDensity
    rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ measurableSet_Iic,
      Measure.restrict_univ, Measure.restrict_restrict measurableSet_Iic]
    congr 1
    congr 1
    ext r
    simp only [mem_inter_iff, mem_Iic, mem_Icc]
    tauto
  rw [heq, scalarCoefficientClockDensity_Iic c hint hpos 1 (by norm_num),
    div_self htotal.ne', ENNReal.ofReal_one]

theorem scalarCoefficientClockDensity_probability (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Icc (0 : ℝ) 1, 0 < c q) :
    IsProbabilityMeasure (scalarCoefficientClockDensity c) :=
  ⟨scalarCoefficientClockDensity_univ c hint hpos⟩

end HexagonPaper
