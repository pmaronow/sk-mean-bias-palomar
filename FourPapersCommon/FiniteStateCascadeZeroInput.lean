module
public import FourPapersCommon.FiniteStateCascadePairs
public import FourPapersCommon.FiniteStateCascadePrefix

@[expose] public section

/-! Zero covariance steps are actual identity transitions and leave the
Gaussian terminal cascade unchanged, irrespective of their real mass. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1000000
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianStep_zero_input (a : ℝ)
    (F : FiniteStateField S→ℝ) :
    finiteStateGaussianStep a (0 : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) F=F := by
  funext H
  unfold finiteStateGaussianStep sourceLogAverage
  by_cases ha : a=0
  · simp [ha]
  · simp [ha,Real.exp_ne_zero,ha]

theorem finiteStateGaussianRawKernel_zero_input :
    finiteStateGaussianRawKernel (0 : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)=
      Kernel.id := by
  ext H : 1
  rw [finiteStateGaussianRawKernel_apply]
  simp [Kernel.id_apply]

theorem finiteStateGaussianStepKernel_zero_input (a : ℝ)
    (F : FiniteStateField S→ℝ) (hF : Measurable F) :
    finiteStateGaussianStepKernel a (0 : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) F=
      Kernel.id := by
  ext H : 1
  rw [finiteStateGaussianStepKernel_apply a 0 F hF]
  unfold finiteStateGaussianStepLaw
  rw [finiteStateGaussianRawKernel_zero_input]
  simp [Measure.tilted,Kernel.id_apply,dirac_withDensity,Real.exp_ne_zero]

variable [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem finiteStateGaussianTerminalCascade_zero_step (V : S→ℝ) (a : ℕ→ℝ)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (p : ℕ)
    (hp : L p=0) :
    finiteStateGaussianTerminalCascade V a L (p+1)=
      finiteStateGaussianTerminalCascade V a L p := by
  change finiteStateGaussianStep (a p) (L p) (finiteStateGaussianTerminalCascade V a L p)=_
  rw [hp,finiteStateGaussianStep_zero_input]

theorem finiteStateGaussianCascadeKernel_zero_step (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0 ≤ a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (p : ℕ)
    (hp : L p=0) :
    finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) p=Kernel.id := by
  unfold finiteStateGaussianCascadeKernel
  rw [hp]
  exact finiteStateGaussianStepKernel_zero_input _ _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous.measurable

private theorem sourceKernelExpectation_drop_first_id
    (Q : ℕ→Kernel (FiniteStateField S) (FiniteStateField S)) (hQ : Q 0=Kernel.id)
    (w : FiniteStateField S→ℝ) (hw : Measurable w) (j : ℕ) :
    sourceKernelExpectation Q (j+1) w=
      sourceKernelExpectation (fun p=>Q (p+1)) j w := by
  induction j with
  | zero =>
    funext H
    simp [sourceKernelExpectation,hQ,Kernel.id_apply,integral_dirac' w H hw.stronglyMeasurable]
  | succ j ih =>
    funext H
    change (∫y,sourceKernelExpectation Q (j+1) w y∂Q (j+1) H)=
      ∫y,sourceKernelExpectation (fun p=>Q (p+1)) j w y∂Q (j+1) H
    rw [ih]

theorem finiteStateCascadePairMoment_zero_shift (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0 ≤ a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S) (p q : ℕ)
    (hp : L p=0) (H K M : FiniteStateField S) :
    finiteStateCascadePairMoment V a L p (q+1) H K M=
      finiteStateCascadePairMoment V a L (p+1) q H K M := by
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L p).continuous_fderiv (by norm_num)
  have hw : Measurable (fun y : FiniteStateField S=>
      fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y K*
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L p) y M) :=
    ((hd.clm_apply continuous_const).mul (hd.clm_apply continuous_const)).measurable
  have hh := sourceKernelExpectation_drop_first_id
    (fun r=>finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (p+r))
    (by simpa only [Nat.add_zero] using finiteStateGaussianCascadeKernel_zero_step V a ha L p hp)
    _ hw q
  unfold finiteStateCascadePairMoment
  rw [finiteStateGaussianTerminalCascade_zero_step V a L p hp]
  simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using congrFun hh H

theorem finiteStateCascadePairMoment_zero_segment (V : S→ℝ) (a : ℕ→ℝ)
    (ha : ∀j,0 ≤ a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (p d J : ℕ) (hpd : p ≤ d) (hdJ : d ≤ J)
    (hL : ∀r,p ≤ r → r < d → L r=0) (H K M : FiniteStateField S) :
    finiteStateCascadePairMoment V a L p (J-p) H K M=
      finiteStateCascadePairMoment V a L d (J-d) H K M := by
  induction d,hpd using Nat.le_induction with
  | base => rfl
  | succ d hpd ih =>
    have hd : d ≤ J := by omega
    rw [ih hd (fun r hr hrd=>hL r hr (by omega)),
      show J-d=(J-(d+1))+1 by omega]
    exact finiteStateCascadePairMoment_zero_shift V a ha L d (J-(d+1))
      (hL d hpd (by omega)) H K M

end FourPapersCommon
