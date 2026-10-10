module
public import FourPapersCommon.FiniteStateCovarianceSchedule

@[expose] public section

/-! Exact signed derivative recurrence for the actual covariance schedule.
The preceding potential's derivative is propagated by its actual normalized
Gaussian step, and each covariance direction contributes its variance generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 900000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianScheduledTerminal_time_succ [Nonempty S]
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (j : ℕ) (t : ℝ) (ht : t∈Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianScheduledTerminalTime V a ha A up (j+1) t H =
      if up j then
        finiteStateGaussianPositivePriorTimeMean (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (A j) t H+
        finiteStateGaussianVarianceGenerator (a j) t (A j)
          (finiteStateGaussianScheduledTerminalCascade V a A up j t) H
      else
        finiteStateGaussianPriorTimeMean (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (A j) t H-
        finiteStateGaussianVarianceGenerator (a j) (1-t) (A j)
          (finiteStateGaussianScheduledTerminalCascade V a A up j t) H := by
  have hd:=hasDerivAt_finiteStateGaussianScheduledTerminal_time V a ha A up (j+1) t ht H
  cases he : up j
  · simp only [he,Bool.false_eq_true,ite_false]
    have hi:=hasDerivAt_finiteStateGaussianStep_time
      (finiteStateGaussianScheduledTerminalData V a ha A up j) (a j) (A j) t ht H
    have hi' : HasDerivAt (fun u=>finiteStateGaussianScheduledTerminalCascade V a A up (j+1) u H)
        (finiteStateGaussianPriorTimeMean (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (A j) t H-
        finiteStateGaussianVarianceGenerator (a j) (1-t) (A j)
          (finiteStateGaussianScheduledTerminalCascade V a A up j t) H) t := by
      simpa only [finiteStateGaussianScheduledTerminalCascade,finiteStateScheduleScale,he,
        Bool.false_eq_true,ite_false] using hi
    exact hd.unique hi'
  · simp only [he,ite_true]
    have hi:=hasDerivAt_finiteStateGaussianStep_positive_time
      (finiteStateGaussianScheduledTerminalData V a ha A up j) (a j) (A j) t ht H
    have hi' : HasDerivAt (fun u=>finiteStateGaussianScheduledTerminalCascade V a A up (j+1) u H)
        (finiteStateGaussianPositivePriorTimeMean (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (A j) t H+
        finiteStateGaussianVarianceGenerator (a j) t (A j)
          (finiteStateGaussianScheduledTerminalCascade V a A up j t) H) t := by
      simpa only [finiteStateGaussianScheduledTerminalCascade,finiteStateScheduleScale,he,ite_true] using hi
    exact hd.unique hi'

end FourPapersCommon
