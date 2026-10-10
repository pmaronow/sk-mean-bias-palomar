module
public import QuantitativePaper.Completion
public import QuantitativePaper.ScalarFloorContinuity
public import FourPapersCommon.NormalizedCGFGlobal

@[expose] public section

/-! Actual completed fractional pressure has its removable value at zero.
All real exponential moments of the finite completed SK model are proved,
so the normalized pressure is analytic, including at zero tilt. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 800000

theorem integrableExpSet_completedLogPartition (n : ℕ) (β : ℝ) :
    integrableExpSet (completedLogPartition n β) (completionLaw n) = univ := by
  ext s
  simp only [integrableExpSet, mem_setOf_eq, mem_univ, iff_true]
  exact integrable_exp_completedLogPartition n β s

theorem completedFractionalPressure_eq_normalized (n : ℕ) (β s : ℝ) :
    completedFractionalPressure n β s =
      normalizedCGF (completionLaw n) (completedLogPartition n β) s / (n : ℝ) := by
  by_cases hs : s = 0
  · subst s
    rw [normalizedCGF_zero _ _ (by simp [integrableExpSet_completedLogPartition]),
      integral_completedLogPartition]
    simp only [completedFractionalPressure, ite_true, pressure]
  · unfold completedFractionalPressure
    rw [ite_eq_right hs, normalizedCGF_of_ne _ _ hs]
    ring

theorem analyticAt_completedFractionalPressure (n : ℕ) (β s : ℝ) :
    AnalyticAt ℝ (completedFractionalPressure n β) s := by
  have he : completedFractionalPressure n β = fun s =>
      normalizedCGF (completionLaw n) (completedLogPartition n β) s / (n : ℝ) :=
    funext (completedFractionalPressure_eq_normalized n β)
  rw [he]
  exact (analyticAt_normalizedCGF _ _ (integrableExpSet_completedLogPartition n β) s).div_const

theorem continuous_completedFractionalPressure (n : ℕ) (β : ℝ) :
    Continuous (completedFractionalPressure n β) :=
  continuous_iff_continuousAt.mpr fun s => (analyticAt_completedFractionalPressure n β s).continuousAt

theorem continuousOn_scalar_fractional_gap (n : ℕ) (β : ℝ) :
    ContinuousOn (fun s => constrainedParisiValue β s - completedFractionalPressure n β s)
      (Icc (0 : ℝ) 1) :=
  (continuousOn_constrainedParisiValue β).sub (continuous_completedFractionalPressure n β).continuousOn

end QuantitativePaper
