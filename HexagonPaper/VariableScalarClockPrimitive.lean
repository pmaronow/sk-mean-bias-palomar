module
public import HexagonPaper.VariableScalarClockPrimitiveBasic
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Order.Hom.Set

@[expose] public section

/-! The actual normalized primitive clock is an increasing order
homeomorphism. The measurable bounded coefficient supplies integrability;
the clock itself is not an additional hypothesis. -/
noncomputable section
open Set MeasureTheory
namespace HexagonPaper

def scalarCoefficientNormalizedClock (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) (q : Paper.Overlap) : Paper.Overlap := by
  have htotal := scalarCoefficient_total_pos c hint hpos
  have hmono := (scalarCoefficient_primitive_strictMonoOn c hint hpos).monotoneOn
  have hlo := hmono (by norm_num : (0 : ℝ) ∈ Icc 0 1) q.property q.property.1
  have hhi := hmono q.property (by norm_num : (1 : ℝ) ∈ Icc 0 1) q.property.2
  refine ⟨scalarCoefficientPrimitive c q / scalarCoefficientPrimitive c 1, ?_, ?_⟩
  · apply div_nonneg _ htotal.le
    simpa only [scalarCoefficientPrimitive, intervalIntegral.integral_same] using hlo
  · exact (div_le_one htotal).2 hhi

theorem scalarCoefficientNormalizedClock_strictMono (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    StrictMono (scalarCoefficientNormalizedClock c hint hpos) := by
  intro x y hxy
  change scalarCoefficientPrimitive c x / scalarCoefficientPrimitive c 1 <
    scalarCoefficientPrimitive c y / scalarCoefficientPrimitive c 1
  exact (div_lt_div_iff_of_pos_right (scalarCoefficient_total_pos c hint hpos)).2
    (scalarCoefficient_primitive_strictMonoOn c hint hpos x.property y.property hxy)

theorem scalarCoefficientNormalizedClock_surjective (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    Function.Surjective (scalarCoefficientNormalizedClock c hint hpos) := by
  intro y
  let f : ℝ → ℝ := fun q => scalarCoefficientPrimitive c q / scalarCoefficientPrimitive c 1
  have htotal := scalarCoefficient_total_pos c hint hpos
  have hf : ContinuousOn f (Icc (0 : ℝ) 1) :=
    (scalarCoefficient_primitive_continuousOn c hint).div_const _
  have h0 : f 0 = 0 := by simp only [f, scalarCoefficientPrimitive,
    intervalIntegral.integral_same, zero_div]
  have h1 : f 1 = 1 := div_self htotal.ne'
  have hy : (y : ℝ) ∈ Icc (f 0) (f 1) := by rw [h0, h1]; exact y.property
  obtain ⟨x, hx, hxy⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  exact hxy

def scalarCoefficientClock (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) : Paper.Overlap ≃o Paper.Overlap :=
  StrictMono.orderIsoOfSurjective (scalarCoefficientNormalizedClock c hint hpos)
    (scalarCoefficientNormalizedClock_strictMono c hint hpos)
    (scalarCoefficientNormalizedClock_surjective c hint hpos)

theorem scalarCoefficientClock_apply (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) (q : Paper.Overlap) :
    (scalarCoefficientClock c hint hpos q : ℝ) =
      (∫ r in (0 : ℝ)..(q : ℝ), c r) / (∫ r in (0 : ℝ)..1, c r) := rfl

theorem scalarCoefficientClock_endpoints (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    scalarCoefficientClock c hint hpos 0 = 0 ∧
      scalarCoefficientClock c hint hpos 1 = 1 := by
  constructor
  · apply Subtype.ext
    rw [scalarCoefficientClock_apply]
    simp
  · apply Subtype.ext
    rw [scalarCoefficientClock_apply]
    exact div_self (scalarCoefficient_total_pos c hint hpos).ne'

theorem scalarCoefficientClock_continuous (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    Continuous (scalarCoefficientClock c hint hpos) ∧
      Continuous (scalarCoefficientClock c hint hpos).symm :=
  ⟨(scalarCoefficientClock c hint hpos).continuous,
    (scalarCoefficientClock c hint hpos).symm.continuous⟩

theorem scalarCoefficientClock_temperature (c : ℝ → ℝ)
    (hint : IntervalIntegrable c volume 0 1)
    (hpos : ∀ q ∈ Ioo (0 : ℝ) 1, 0 < c q) :
    0 < Real.sqrt (scalarCoefficientPrimitive c 1) ∧
      (Real.sqrt (scalarCoefficientPrimitive c 1)) ^ 2 = scalarCoefficientPrimitive c 1 :=
  ⟨Real.sqrt_pos.2 (scalarCoefficient_total_pos c hint hpos),
    Real.sq_sqrt (scalarCoefficient_total_pos c hint hpos).le⟩

end HexagonPaper
