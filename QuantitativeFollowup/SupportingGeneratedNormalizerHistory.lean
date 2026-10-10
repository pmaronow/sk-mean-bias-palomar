module
public import QuantitativeFollowup.FollowupCavityGeneratedForestReindex
public import QuantitativeFollowup.FollowupCavityGeneratedMarkProgramBudget

@[expose] public section

/-! The normalizer mark is an actual unrestricted free draw appended to
all old coordinates, followed by its prescribed root attenuation. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
variable {m : ℕ}
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def printedGeneratedNormalizerProgram (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (a : ℝ) (ha : a∈Icc (0 : ℝ) 1) : CavityGeneratedMarkProgram Paper.Overlap (m+1) :=
  .attenuate (.fresh P univ) (fun _ => ENNReal.ofReal a)
    (fun _ => ENNReal.ofReal_le_one.mpr ha.2)

theorem printedGeneratedNormalizerProgram_measure
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (ν : Measure Paper.Overlap) :
    (printedGeneratedNormalizerProgram P a ha).measure ν =
      ENNReal.ofReal a • ((P.measure ν).prod ν).map cavityGeneratedHistoryAppend := by
  simp only [printedGeneratedNormalizerProgram,CavityGeneratedMarkProgram.measure,
    Measure.restrict_univ,withDensity_const]

theorem printedGeneratedNormalizerProgram_integral
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (ν : Measure Paper.Overlap)
    (Φ : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ) (hΦ : Measurable Φ) :
    (∫H, Φ H ∂(printedGeneratedNormalizerProgram P a ha).measure ν) =
      a*(∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
        Φ (Fin.snoc z.1 z.2) ∂(P.measure ν).prod ν) := by
  rw [printedGeneratedNormalizerProgram_measure,integral_smul_measure,
    integral_map cavityGeneratedHistoryAppend_measurable.aemeasurable hΦ.aestronglyMeasurable,
    ENNReal.toReal_ofReal ha.1]
  rfl

theorem printedGeneratedNormalizerProgram_budget
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) :
    (printedGeneratedNormalizerProgram P a ha).budget = P.budget := rfl

theorem printedGeneratedNormalizerProgram_actual_mark_budget
    (P : CavityGeneratedMarkProgram Paper.Overlap m) (a : ℝ)
    (ha : a∈Icc (0 : ℝ) 1) (ν : Measure Paper.Overlap)
    [SFinite ν] (hν : ν univ ≤ 1) :
    cavityGeneratedMarkBudget ν ((printedGeneratedNormalizerProgram P a ha).measure ν)
      cavityGeneratedHistoryMarks (P.budget : ℝ≥0∞) :=
  (printedGeneratedNormalizerProgram P a ha).actual_mark_budget ν hν

end QuantitativeFollowup
