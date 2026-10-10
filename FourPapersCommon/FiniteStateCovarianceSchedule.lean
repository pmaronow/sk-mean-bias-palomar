module
public import FourPapersCommon.GenericFiniteStateCascadeInterpolation

@[expose] public section

/-! Genuine finite Gaussian cascades with independently increasing and
 decreasing covariance directions. The actual time regularity is constructed
through the logarithmic Gaussian steps, including zero masses and directions.
This permits coefficient perturbations while keeping a fixed covariance part. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1200000
variable {S I : Type*} [Fintype S] [Fintype I]

def finiteStateGaussianPositiveTimeStep
    {F : ℝ → FiniteStateField S → ℝ} {C B K : ℝ≥0}
    (d : FiniteStateGaussianTimeData F C B K)
    (a : ℝ) (ha : 0≤a) (A : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    FiniteStateGaussianTimeData (fun t H => finiteStateGaussianStep a (Real.sqrt t • A) (F t) H)
      C (B+2*Real.toNNReal a*C^2) (K+finiteStateGaussianGeneratorBound a A C B) := by
  have he : (fun t H => finiteStateGaussianStep a (Real.sqrt (1-(1-t)) • A)
      (fun H => F (1-(1-t)) H) H) =
      (fun t H => finiteStateGaussianStep a (Real.sqrt t • A) (F t) H) := by
    funext t H
    simp only [sub_sub_cancel]
  exact he ▸ finiteStateGaussianTimeReverse
    (finiteStateGaussianTimeStep (finiteStateGaussianTimeReverse d) a ha A)

def finiteStateScheduleScale (up : Bool) (t : ℝ) : ℝ :=
  if up then Real.sqrt t else Real.sqrt (1-t)

def finiteStateGaussianScheduledTerminalCascade [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) : ℕ → ℝ → FiniteStateField S → ℝ
  | 0 => fun _ => SpinGlass.AT.gtStateLogPartition V
  | j+1 => fun t H => finiteStateGaussianStep (a j)
      (finiteStateScheduleScale (up j) t • A j)
      (finiteStateGaussianScheduledTerminalCascade V a A up j t) H

def finiteStateScheduleTimeBound (a : ℕ → ℝ)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) : ℕ → ℝ≥0
  | 0 => 0
  | j+1 => finiteStateScheduleTimeBound a A j+
    finiteStateGaussianGeneratorBound (a j) (A j) 1 (finiteStateInterpolationHessianBound a j)

def finiteStateGaussianScheduledTerminalData [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) : (j : ℕ) →
    FiniteStateGaussianTimeData (finiteStateGaussianScheduledTerminalCascade V a A up j)
      1 (finiteStateInterpolationHessianBound a j) (finiteStateScheduleTimeBound a A j)
  | 0 => finiteStateGaussianTerminalTimeData V
  | j+1 => by
      cases hup : up j
      · simpa only [finiteStateGaussianScheduledTerminalCascade,finiteStateScheduleScale,hup,
          Bool.false_eq_true,ite_false,finiteStateInterpolationHessianBound,finiteStateScheduleTimeBound] using
          finiteStateGaussianTimeStep (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (ha j) (A j)
      · simpa only [finiteStateGaussianScheduledTerminalCascade,finiteStateScheduleScale,hup,
          ite_true,finiteStateInterpolationHessianBound,finiteStateScheduleTimeBound] using
          finiteStateGaussianPositiveTimeStep (finiteStateGaussianScheduledTerminalData V a ha A up j)
          (a j) (ha j) (A j)

def finiteStateGaussianScheduledTerminalTime [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) (j : ℕ) (t : ℝ) (H : FiniteStateField S) : ℝ :=
  (finiteStateGaussianScheduledTerminalData V a ha A up j).time t H

theorem hasDerivAt_finiteStateGaussianScheduledTerminal_time [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianScheduledTerminalCascade V a A up j u H)
      (finiteStateGaussianScheduledTerminalTime V a ha A up j t H) t :=
  (finiteStateGaussianScheduledTerminalData V a ha A up j).time_hasDeriv t ht H

theorem continuousOn_finiteStateGaussianScheduledTerminal_time [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) (j : ℕ) :
    ContinuousOn (fun p : ℝ×FiniteStateField S =>
      finiteStateGaussianScheduledTerminalTime V a ha A up j p.1 p.2)
      (finiteStateGaussianTimeDomain S) :=
  (finiteStateGaussianScheduledTerminalData V a ha A up j).time_cont

theorem abs_finiteStateGaussianScheduledTerminal_time_le [Nonempty S]
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀j,0≤a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (up : ℕ → Bool) (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    |finiteStateGaussianScheduledTerminalTime V a ha A up j t H| ≤ finiteStateScheduleTimeBound a A j :=
  (finiteStateGaussianScheduledTerminalData V a ha A up j).time_bound t ht H

end FourPapersCommon
