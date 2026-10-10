module
public import FourPapersCommon.GenericFiniteStateCascadeTimePreservation
public import FourPapersCommon.GenericFiniteStateCascadeTimeReflection

@[expose] public section

/-! Actual covariance interpolation of the entire finite terminal cascade.
The regularity record is constructed inductively, rather than assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology NNReal ContDiff BigOperators
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]

def finiteStateGaussianInterpolatedTerminalCascade (V : S → ℝ) (a : ℕ → ℝ)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (H : FiniteStateField S) : ℝ :=
  finiteStateGaussianTerminalCascade V a (fun i => Real.sqrt (1-t) • A i) j H

def finiteStateInterpolationHessianBound (a : ℕ → ℝ) : ℕ → ℝ≥0
  | 0 => 2
  | j+1 => finiteStateInterpolationHessianBound a j+2*Real.toNNReal (a j)*(1 : ℝ≥0)^2

def finiteStateInterpolationTimeBound (a : ℕ → ℝ)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) : ℕ → ℝ≥0
  | 0 => 0
  | j+1 => finiteStateInterpolationTimeBound a A j+
    finiteStateGaussianGeneratorBound (a j) (A j) 1 (finiteStateInterpolationHessianBound a j)

def finiteStateGaussianTerminalCascadeTimeData
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    (j : ℕ) → FiniteStateGaussianTimeData (finiteStateGaussianInterpolatedTerminalCascade V a A j)
      1 (finiteStateInterpolationHessianBound a j) (finiteStateInterpolationTimeBound a A j)
  | 0 => finiteStateGaussianTerminalTimeData V
  | j+1 => finiteStateGaussianTimeStep (finiteStateGaussianTerminalCascadeTimeData V a ha A j)
    (a j) (ha j) (A j)

def finiteStateGaussianTerminalCascadeTime (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (H : FiniteStateField S) : ℝ :=
  (finiteStateGaussianTerminalCascadeTimeData V a ha A j).time t H

@[simp] theorem finiteStateGaussianTerminalCascadeTime_zero (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (t : ℝ) (H : FiniteStateField S) : finiteStateGaussianTerminalCascadeTime V a ha A 0 t H = 0 := rfl

theorem finiteStateGaussianTerminalCascadeTime_succ (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascadeTime V a ha A (j+1) t H =
      finiteStateGaussianInputMean (a j)
        (fun z => finiteStateGaussianInterpolatedTerminalCascade V a A j t (H+Real.sqrt (1-t) • A j z))
        (fun z => finiteStateGaussianTerminalCascadeTime V a ha A j t (H+Real.sqrt (1-t) • A j z))-
      finiteStateGaussianVarianceGenerator (a j) (1-t) (A j)
        (finiteStateGaussianInterpolatedTerminalCascade V a A j t) H := rfl

theorem hasDerivAt_finiteStateGaussianTerminalCascade_time
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianInterpolatedTerminalCascade V a A j u H)
      (finiteStateGaussianTerminalCascadeTime V a ha A j t H) t :=
  (finiteStateGaussianTerminalCascadeTimeData V a ha A j).time_hasDeriv t ht H

theorem continuousOn_finiteStateGaussianTerminalCascade_time
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) (j : ℕ) :
    ContinuousOn (fun p : ℝ×FiniteStateField S => finiteStateGaussianTerminalCascadeTime V a ha A j p.1 p.2)
      (finiteStateGaussianTimeDomain S) :=
  (finiteStateGaussianTerminalCascadeTimeData V a ha A j).time_cont

theorem abs_finiteStateGaussianTerminalCascade_time_le
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    |finiteStateGaussianTerminalCascadeTime V a ha A j t H| ≤ finiteStateInterpolationTimeBound a A j :=
  (finiteStateGaussianTerminalCascadeTimeData V a ha A j).time_bound t ht H

theorem hasDerivAt_finiteStateGaussianTerminalCascade_outer_time
    {I' : Type*} [Fintype I']
    (V : S → ℝ) (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput I' →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianStep 0 (Real.sqrt u • M)
      (finiteStateGaussianInterpolatedTerminalCascade V a A j u) H)
      (finiteStateGaussianPositivePriorTimeMean (finiteStateGaussianTerminalCascadeTimeData V a ha A j) 0 M t H+
        finiteStateGaussianVarianceGenerator 0 t M (finiteStateGaussianInterpolatedTerminalCascade V a A j t) H) t :=
  hasDerivAt_finiteStateGaussianStep_positive_time (finiteStateGaussianTerminalCascadeTimeData V a ha A j) 0 M t ht H

end FourPapersCommon
