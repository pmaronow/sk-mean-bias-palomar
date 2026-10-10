module
public import FourPapersCommon.FiniteStateCovarianceScheduleFormula
public import FourPapersCommon.FiniteStateCascadeInterpolationTrace

@[expose] public section

/-! Signed covariance responses for genuine Gaussian schedules. All
expectations are under the actual normalized terminal-cascade kernels. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal ContDiff
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1600000
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

omit [DecidableEq I] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem finiteStateGaussianScheduledTerminalCascade_eq_current
    (V : S→ℝ) (a : ℕ→ℝ)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (j : ℕ) (t : ℝ) :
    finiteStateGaussianScheduledTerminalCascade V a A up j t =
      finiteStateGaussianTerminalCascade V a (fun i=>finiteStateScheduleScale (up i) t • A i) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [finiteStateGaussianScheduledTerminalCascade,finiteStateGaussianTerminalCascade,
      finiteStateGaussianCascade,ih]

theorem finiteStateGaussianVarianceGenerator_eq_response_current
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (L : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (j : ℕ) (v : ℝ) (A : FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (hL : L j=Real.sqrt v • A) (H : FiniteStateField S) :
    finiteStateGaussianVarianceGenerator (a j) v A
      (finiteStateGaussianTerminalCascade V a L j) H =
      finiteStateCascadeCovarianceResponse V a L j 1 H A/2 := by
  let U:=finiteStateGaussianTerminalCascade V a L j
  have hC : ∀y,‖fderiv ℝ U y‖≤(1 : ℝ≥0) :=
    fun y=>norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
  have hB:=finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  rw [finiteStateGaussianVarianceGenerator_eq_stepMean (a j) v A U hB.1 1
    (finiteStateCascadeHessianBound a j) hC hB.2 H,
    finiteStateCascadeCovarianceResponse_eq_kernelExpectation V a ha L j 1 H A]
  simp_rw [finiteStateGaussianGeneratorField_eq_trace]
  rw [integral_div]
  congr 1
  simp only [sourceKernelExpectation,Nat.add_zero]
  rw [finiteStateGaussianCascadeKernel,finiteStateGaussianStepKernel_apply
    (a j) (L j) (finiteStateGaussianCascade a L (gtStateLogPartition V) j)
      hB.1.continuous.measurable,hL]
  rfl

theorem finiteStateGaussianScheduledTerminal_time_succ_kernel
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (j : ℕ) (t : ℝ) (ht : t∈Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianScheduledTerminalTime V a ha A up (j+1) t H =
      (∫y,finiteStateGaussianScheduledTerminalTime V a ha A up j t y
        ∂finiteStateGaussianCascadeKernel a (fun i=>finiteStateScheduleScale (up i) t • A i)
          (gtStateLogPartition V) j H)+
      (if up j then (1 : ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a (fun i=>finiteStateScheduleScale (up i) t • A i)
          j 1 H (A j)/2 := by
  let L:=fun i=>finiteStateScheduleScale (up i) t • A i
  let U:=finiteStateGaussianScheduledTerminalCascade V a A up j t
  have hT : Continuous (finiteStateGaussianScheduledTerminalTime V a ha A up j t) :=
    continuousOn_univ.mp ((continuousOn_finiteStateGaussianScheduledTerminal_time V a ha A up j).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun y _=>⟨ht,mem_univ y⟩))
  have hU:=contDiff_two_finiteStateGaussianTerminalCascade V a ha L j
  have hUc : ContDiff ℝ 2 U := by
    simpa only [U,finiteStateGaussianScheduledTerminalCascade_eq_current,L] using hU
  have hQ : finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H =
      finiteStateGaussianStepLaw (a j) (L j) U H := by
    rw [finiteStateGaussianCascadeKernel,finiteStateGaussianStepKernel_apply (a j) (L j)
      (finiteStateGaussianCascade a L (gtStateLogPartition V) j)
      (show Measurable (finiteStateGaussianCascade a L (gtStateLogPartition V) j) from hU.continuous.measurable)]
    dsimp only [U]
    rw [finiteStateGaussianScheduledTerminalCascade_eq_current]
    rfl
  rw [finiteStateGaussianScheduledTerminal_time_succ V a ha A up j t ht H]
  cases he : up j
  · simp only [Bool.false_eq_true,ite_false,neg_one_mul]
    rw [finiteStateGaussianPriorTimeMean]
    change finiteStateGaussianInputMean (a j) (fun z=>U (H+Real.sqrt (1-t) • A j z))
        (fun z=>finiteStateGaussianScheduledTerminalTime V a ha A up j t (H+Real.sqrt (1-t) • A j z))-
      finiteStateGaussianVarianceGenerator (a j) (1-t) (A j) U H = _
    rw [finiteStateGaussianInputMean_field_eq_stepLaw (a j) (1-t) (A j) U _
        hUc.continuous.measurable hT.measurable H]
    have hLj : L j=Real.sqrt (1-t) • A j := by simp only [L,finiteStateScheduleScale,he,Bool.false_eq_true,ite_false]
    have hgen:=finiteStateGaussianVarianceGenerator_eq_response_current V a ha L j (1-t) (A j) hLj H
    rw [←finiteStateGaussianScheduledTerminalCascade_eq_current V a A up j t] at hgen
    change _-_=_+-_/2
    rw [hgen]
    rw [hQ,hLj]
    ring
  · simp only [ite_true,one_mul]
    rw [finiteStateGaussianPositivePriorTimeMean]
    change finiteStateGaussianInputMean (a j) (fun z=>U (H+Real.sqrt t • A j z))
        (fun z=>finiteStateGaussianScheduledTerminalTime V a ha A up j t (H+Real.sqrt t • A j z))+
      finiteStateGaussianVarianceGenerator (a j) t (A j) U H = _
    rw [finiteStateGaussianInputMean_field_eq_stepLaw (a j) t (A j) U _
        hUc.continuous.measurable hT.measurable H]
    have hLj : L j=Real.sqrt t • A j := by simp only [L,finiteStateScheduleScale,he,ite_true]
    have hgen:=finiteStateGaussianVarianceGenerator_eq_response_current V a ha L j t (A j) hLj H
    rw [←finiteStateGaussianScheduledTerminalCascade_eq_current V a A up j t] at hgen
    rw [hgen,hQ,hLj]

theorem finiteStateGaussianScheduledTerminal_time_eq_responses
    (V : S→ℝ) (a : ℕ→ℝ) (ha : ∀j,0≤a j)
    (A : ℕ→FiniteStateGaussianInput I→L[ℝ]FiniteStateField S)
    (up : ℕ→Bool) (J : ℕ) (t : ℝ) (ht : t∈Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianScheduledTerminalTime V a ha A up J t H =
      (1/2 : ℝ)*∑j∈Finset.range J,(if up j then (1 : ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a (fun i=>finiteStateScheduleScale (up i) t • A i)
          j (J-j) H (A j) := by
  classical
  let L:=fun i=>finiteStateScheduleScale (up i) t • A i
  induction J generalizing H with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,mul_zero]
    rfl
  | succ J ih =>
    rw [finiteStateGaussianScheduledTerminal_time_succ_kernel V a ha A up J t ht H]
    simp_rw [ih]
    rw [integral_const_mul]
    let _:=isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L J
    have hi (j : ℕ) : Integrable (fun y=>(if up j then (1 : ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j))
        (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H) :=
      (source_bounded_integrable _ _
        (finiteStateCascadeCovarianceResponse_measurable V a ha L j (J-j) (A j)) _
        (finiteStateCascadeCovarianceResponse_abs_le V a ha L j (J-j) (A j))).const_mul _
    rw [integral_finsetSum (Finset.range J) (fun j _=>hi j)]
    have he : (∑j∈Finset.range J,∫y,(if up j then (1 : ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H) =
        ∑j∈Finset.range J,(if up j then (1 : ℝ) else -1)*
          finiteStateCascadeCovarianceResponse V a L j (J+1-j) H (A j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
      have hJ : j+(J-j)=J := by have := Finset.mem_range.mp hj; omega
      have hh:=finiteStateCascadeCovarianceResponse_succ V a ha L j (J-j) (A j) H
      rw [hJ] at hh
      have hidx : J-j+1=J+1-j := by have := Finset.mem_range.mp hj; omega
      rw [hidx] at hh
      rw [←hh]
    change (1/2 : ℝ)*(∑j∈Finset.range J,∫y,(if up j then (1 : ℝ) else -1)*
        finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H)+
      (if up J then (1 : ℝ) else -1)*finiteStateCascadeCovarianceResponse V a L J 1 H (A J)/2 = _
    rw [he,Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left]
    ring

end FourPapersCommon
