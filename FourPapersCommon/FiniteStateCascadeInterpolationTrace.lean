module
public import FourPapersCommon.GenericFiniteStateCascadeInterpolation
public import FourPapersCommon.FiniteStateCascadeResponses
public import FourPapersCommon.FiniteStateCascadeGenerators

@[expose] public section

/-! The true covariance-time derivative of the actual Gaussian cascade equals
its finite sum of propagated normalized covariance responses. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators NNReal ContDiff
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
set_option maxHeartbeats 1600000
variable {S I : Type*} [Fintype S] [Fintype I] [DecidableEq I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

 theorem finiteStateGaussianGeneratorField_eq_trace (a : ℝ)
    (A : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (H : FiniteStateField S) :
    finiteStateGaussianGeneratorField a A F H =
      (finiteStateHessianTrace A F H+a*finiteStateGradientSquareTrace A F H)/2 := by
  classical
  unfold finiteStateGaussianGeneratorField finiteStateHessianTrace finiteStateGradientSquareTrace
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Fintype.sum_equiv (Fintype.equivFin I).symm _ _ (fun i => by
    simp only [finiteStateGaussianBasis, OrthonormalBasis.reindex_apply,
      EuclideanSpace.basisFun_apply])

 theorem finiteStateGaussianVarianceGenerator_eq_response (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (H : FiniteStateField S) :
    finiteStateGaussianVarianceGenerator (a j) (1-t) (A j)
      (finiteStateGaussianInterpolatedTerminalCascade V a A j t) H =
      finiteStateCascadeCovarianceResponse V a (fun i => Real.sqrt (1-t) • A i) j 1 H (A j)/2 := by
  classical
  let L := fun i => Real.sqrt (1-t) • A i
  let U := finiteStateGaussianTerminalCascade V a L j
  have hC : ∀ y, ‖fderiv ℝ U y‖ ≤ (1 : ℝ≥0) :=
    fun y => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
  have hB := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  change finiteStateGaussianVarianceGenerator (a j) (1-t) (A j) U H =
    finiteStateCascadeCovarianceResponse V a L j 1 H (A j)/2
  rw [finiteStateGaussianVarianceGenerator_eq_stepMean (a j) (1-t) (A j) U hB.1 1
    (finiteStateCascadeHessianBound a j) hC hB.2 H,
    finiteStateCascadeCovarianceResponse_eq_kernelExpectation V a ha L j 1 H (A j)]
  simp_rw [finiteStateGaussianGeneratorField_eq_trace]
  rw [integral_div]
  congr 1
  simp only [sourceKernelExpectation, Nat.add_zero]
  rw [finiteStateGaussianCascadeKernel, finiteStateGaussianStepKernel_apply
    (a j) (L j) (finiteStateGaussianCascade a L (gtStateLogPartition V) j)
      (show Measurable (finiteStateGaussianCascade a L (gtStateLogPartition V) j) from hB.1.continuous.measurable)]
  rfl

 theorem finiteStateCascadeCovarianceResponse_measurable (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (A : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S) :
    Measurable (fun H => finiteStateCascadeCovarianceResponse V a L j q H A) := by
  classical
  have hU := contDiff_two_finiteStateGaussianTerminalCascade V a ha L j
  have h1 := (hU.of_le (by norm_num) : ContDiff ℝ 1 _).continuous_fderiv (by norm_num)
  have h2 := (hU.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuous_fderiv (by norm_num)
  unfold finiteStateCascadeCovarianceResponse
  apply Finset.measurable_sum
  intro i _
  apply sourceKernelExpectation_measurable
  exact (((h2.clm_apply continuous_const).clm_apply continuous_const).add
    (((h1.clm_apply continuous_const).const_mul _).mul (h1.clm_apply continuous_const))).measurable

 theorem finiteStateCascadeCovarianceResponse_abs_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (A : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    |finiteStateCascadeCovarianceResponse V a L j q H A| ≤
      2*(finiteStateGaussianGeneratorBound (a j) A 1 (finiteStateCascadeHessianBound a j) : ℝ) := by
  classical
  let U := finiteStateGaussianTerminalCascade V a L j
  have hU := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  have hC : ∀ y, ‖fderiv ℝ U y‖ ≤ (1 : ℝ≥0) :=
    fun y => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L j)
  have hm : Measurable (finiteStateGaussianGeneratorField (a j) A U) := by
    have h1 := (hU.1.of_le (by norm_num) : ContDiff ℝ 1 U).continuous_fderiv (by norm_num)
    have h2 := (hU.1.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuous_fderiv (by norm_num)
    unfold finiteStateGaussianGeneratorField
    exact (continuous_finsetSum _ (fun i _ =>
      ((h2.clm_apply continuous_const).clm_apply continuous_const).add
        ((h1.clm_apply continuous_const).pow 2 |>.const_mul (a j)))).div_const 2 |>.measurable
  rw [finiteStateCascadeCovarianceResponse_eq_kernelExpectation V a ha L j q H A]
  have hb (y) : |finiteStateHessianTrace A U y+a j*finiteStateGradientSquareTrace A U y| ≤
      2*(finiteStateGaussianGeneratorBound (a j) A 1 (finiteStateCascadeHessianBound a j) : ℝ) := by
    have hg := abs_finiteStateGaussianGeneratorField_le (a j) A U 1
      (finiteStateCascadeHessianBound a j) hC hU.2 y
    rw [finiteStateGaussianGeneratorField_eq_trace, abs_div] at hg
    norm_num at hg
    linarith
  have hm' : Measurable (fun y => finiteStateHessianTrace A U y+a j*finiteStateGradientSquareTrace A U y) := by
    have he : (fun y => finiteStateHessianTrace A U y+a j*finiteStateGradientSquareTrace A U y) =
        fun y => 2*finiteStateGaussianGeneratorField (a j) A U y := by
      funext y
      rw [finiteStateGaussianGeneratorField_eq_trace]
      ring
    rw [he]
    exact hm.const_mul 2
  exact sourceKernelExpectation_abs_le _
    (fun p => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (j+p)) _ hm'
    _ (by positivity) hb q H

 theorem finiteStateCascadeCovarianceResponse_succ (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (A : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L j (q+1) H A =
      ∫ y, finiteStateCascadeCovarianceResponse V a L j q y A
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+q) H := by
  simp_rw [finiteStateCascadeCovarianceResponse_eq_kernelExpectation V a ha L]
  rfl

 theorem finiteStateGaussianTerminalCascadeTime_succ_kernel (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascadeTime V a ha A (j+1) t H =
      (∫ y, finiteStateGaussianTerminalCascadeTime V a ha A j t y
        ∂finiteStateGaussianCascadeKernel a (fun i => Real.sqrt (1-t) • A i)
          (gtStateLogPartition V) j H)-
      finiteStateCascadeCovarianceResponse V a (fun i => Real.sqrt (1-t) • A i) j 1 H (A j)/2 := by
  let L := fun i => Real.sqrt (1-t) • A i
  have hT : Continuous (finiteStateGaussianTerminalCascadeTime V a ha A j t) := by
    exact continuousOn_univ.mp ((continuousOn_finiteStateGaussianTerminalCascade_time V a ha A j).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨ht,mem_univ y⟩))
  have hU := contDiff_two_finiteStateGaussianTerminalCascade V a ha L j
  have hU' : ContDiff ℝ 2 (finiteStateGaussianInterpolatedTerminalCascade V a A j t) := hU
  rw [finiteStateGaussianTerminalCascadeTime_succ,
    finiteStateGaussianInputMean_field_eq_stepLaw (a j) (1-t) (A j)
      (finiteStateGaussianInterpolatedTerminalCascade V a A j t) _ hU'.continuous.measurable
      hT.measurable H,
    finiteStateGaussianVarianceGenerator_eq_response V a ha A j t H]
  have hQ : finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H =
      finiteStateGaussianStepLaw (a j) (Real.sqrt (1-t) • A j)
        (finiteStateGaussianInterpolatedTerminalCascade V a A j t) H := by
    change finiteStateGaussianStepKernel (a j) (L j)
      (finiteStateGaussianCascade a L (gtStateLogPartition V) j) H = _
    exact finiteStateGaussianStepKernel_apply _ _ _
      (show Measurable (finiteStateGaussianCascade a L (gtStateLogPartition V) j) from hU.continuous.measurable) H
  rw [hQ]

 theorem finiteStateGaussianTerminalCascadeTime_eq_responses (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (J : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascadeTime V a ha A J t H =
      (-1/2 : ℝ)*∑ j ∈ Finset.range J,
        finiteStateCascadeCovarianceResponse V a (fun i => Real.sqrt (1-t) • A i) j (J-j) H (A j) := by
  classical
  let L := fun i => Real.sqrt (1-t) • A i
  induction J generalizing H with
  | zero => simp
  | succ J ih =>
    rw [finiteStateGaussianTerminalCascadeTime_succ_kernel V a ha A J t ht H]
    simp_rw [ih]
    rw [integral_const_mul]
    haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L J
    have hi (j : ℕ) : Integrable (fun y => finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j))
        (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H) :=
      source_bounded_integrable _ _ (finiteStateCascadeCovarianceResponse_measurable V a ha L j (J-j) (A j))
        _ (finiteStateCascadeCovarianceResponse_abs_le V a ha L j (J-j) (A j))
    rw [integral_finsetSum (Finset.range J) (fun j _ => hi j)]
    have he : (∑ j ∈ Finset.range J, ∫ y, finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H) =
        ∑ j ∈ Finset.range J, finiteStateCascadeCovarianceResponse V a L j (J+1-j) H (A j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hJ : j+(J-j)=J := by have := Finset.mem_range.mp hj; omega
      have hh := finiteStateCascadeCovarianceResponse_succ V a ha L j (J-j) (A j) H
      rw [hJ] at hh
      have hidx : J-j+1=J+1-j := by have := Finset.mem_range.mp hj; omega
      rw [hidx] at hh
      exact hh.symm
    change (-1/2 : ℝ)*(∑ j ∈ Finset.range J, ∫ y, finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) J H)-
        finiteStateCascadeCovarianceResponse V a L J 1 H (A J)/2 = _
    rw [he, Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel_left]
    ring

variable {I' : Type*} [Fintype I'] [DecidableEq I']

def finiteStateCascadeInterpolationTrace (V : S → ℝ) (a : ℕ → ℝ)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (J : ℕ) (t : ℝ) (M : FiniteStateGaussianInput I' →L[ℝ] FiniteStateField S)
    (H : FiniteStateField S) : ℝ :=
  finiteStateHessianTrace M (finiteStateGaussianInterpolatedTerminalCascade V a A J t) H-
    ∑ j ∈ Finset.range J, finiteStateCascadeCovarianceResponse V a
      (fun i => Real.sqrt (1-t) • A i) j (J-j) H (A j)

 theorem integrable_finiteStateCascadeInterpolationTrace (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (J : ℕ) (t : ℝ) (M : FiniteStateGaussianInput I' →L[ℝ] FiniteStateField S)
    (ν : Measure (FiniteStateField S)) [IsProbabilityMeasure ν] :
    Integrable (finiteStateCascadeInterpolationTrace V a A J t M) ν := by
  classical
  let L := fun i => Real.sqrt (1-t) • A i
  let U := finiteStateGaussianTerminalCascade V a L J
  have hU := finiteStateGaussianTerminalCascade_C2_bounds V a ha L J
  have h2 := (hU.1.fderiv_right (m := (1 : ℕ∞ω)) (by norm_num)).continuous_fderiv (by norm_num)
  have hH : Measurable (finiteStateHessianTrace M U) := by
    unfold finiteStateHessianTrace
    exact (continuous_finsetSum _ (fun i _ =>
      (h2.clm_apply continuous_const).clm_apply continuous_const)).measurable
  have hC : ∀ y, ‖fderiv ℝ U y‖ ≤ (1 : ℝ≥0) :=
    fun y => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L J)
  have hHb (y) : |finiteStateHessianTrace M U y| ≤
      2*(finiteStateGaussianGeneratorBound 0 M 1 (finiteStateCascadeHessianBound a J) : ℝ) := by
    have hh := abs_finiteStateGaussianGeneratorField_le 0 M U 1
      (finiteStateCascadeHessianBound a J) hC hU.2 y
    rw [finiteStateGaussianGeneratorField_eq_trace, zero_mul, add_zero, abs_div] at hh
    norm_num at hh
    linarith
  have hiH := source_bounded_integrable ν _ hH _ hHb
  have hiR (j : ℕ) : Integrable (fun y => finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)) ν :=
    source_bounded_integrable ν _ (finiteStateCascadeCovarianceResponse_measurable V a ha L j (J-j) (A j))
      _ (finiteStateCascadeCovarianceResponse_abs_le V a ha L j (J-j) (A j))
  exact hiH.sub (integrable_finsetSum (Finset.range J) (fun j _ => hiR j))

 theorem hasDerivAt_finiteStateGaussianTerminalCascade_outer_trace (V : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (A : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput I' →L[ℝ] FiniteStateField S)
    (J : ℕ) (t : ℝ) (ht : t ∈ Ioo 0 1) (H : FiniteStateField S) :
    HasDerivAt (fun u => finiteStateGaussianStep 0 (Real.sqrt u • M)
      (finiteStateGaussianInterpolatedTerminalCascade V a A J u) H)
      ((∫ y, finiteStateCascadeInterpolationTrace V a A J t M y
        ∂finiteStateGaussianStepLaw 0 (Real.sqrt t • M)
          (finiteStateGaussianInterpolatedTerminalCascade V a A J t) H)/2) t := by
  classical
  let L := fun i => Real.sqrt (1-t) • A i
  let U := finiteStateGaussianInterpolatedTerminalCascade V a A J t
  let ν := finiteStateGaussianStepLaw 0 (Real.sqrt t • M) U H
  have hU := finiteStateGaussianTerminalCascade_C2_bounds V a ha L J
  have hUc : ContDiff ℝ 2 U := hU.1
  have hC : ∀ y, ‖fderiv ℝ U y‖ ≤ (1 : ℝ≥0) :=
    fun y => norm_fderiv_le_of_lipschitz ℝ (finiteStateGaussianTerminalCascade_lipschitz V a ha L J)
  haveI : IsProbabilityMeasure ν := isProbabilityMeasure_finiteStateGaussianStepLaw 0
    (Real.sqrt t • M) U hUc.continuous.measurable H
    (integrable_exp_finiteStateGaussian_lipschitz U
      (finiteStateGaussianTerminalCascade_lipschitz V a ha L J) _ H 0)
  have hTc : Continuous (finiteStateGaussianTerminalCascadeTime V a ha A J t) :=
    continuousOn_univ.mp ((continuousOn_finiteStateGaussianTerminalCascade_time V a ha A J).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨ht,mem_univ y⟩))
  have hprior : finiteStateGaussianPositivePriorTimeMean
      (finiteStateGaussianTerminalCascadeTimeData V a ha A J) 0 M t H =
      ∫ y, finiteStateGaussianTerminalCascadeTime V a ha A J t y ∂ν := by
    unfold finiteStateGaussianPositivePriorTimeMean
    exact finiteStateGaussianInputMean_field_eq_stepLaw 0 t M U _ hUc.continuous.measurable hTc.measurable H
  have hg : finiteStateGaussianVarianceGenerator 0 t M U H =
      (∫ y, finiteStateHessianTrace M U y ∂ν)/2 := by
    rw [finiteStateGaussianVarianceGenerator_eq_stepMean 0 t M U hUc 1
      (finiteStateCascadeHessianBound a J) hC hU.2 H]
    simp_rw [finiteStateGaussianGeneratorField_eq_trace, zero_mul, add_zero]
    exact integral_div _ _
  have hiR (j : ℕ) : Integrable (fun y => finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j)) ν :=
    source_bounded_integrable ν _ (finiteStateCascadeCovarianceResponse_measurable V a ha L j (J-j) (A j))
      _ (finiteStateCascadeCovarianceResponse_abs_le V a ha L j (J-j) (A j))
  have hiS := integrable_finsetSum (Finset.range J) (fun j _ => hiR j)
  have hiTrace := integrable_finiteStateCascadeInterpolationTrace V a ha A J t M ν
  have hiH : Integrable (finiteStateHessianTrace M U) ν := by
    have hh := hiTrace.add hiS
    convert hh using 1
    funext y
    dsimp [finiteStateCascadeInterpolationTrace,U,L]
    ring
  have htmean : (∫ y, finiteStateGaussianTerminalCascadeTime V a ha A J t y ∂ν) =
      (-1/2 : ℝ)*(∫ y, ∑ j ∈ Finset.range J, finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j) ∂ν) := by
    simp_rw [finiteStateGaussianTerminalCascadeTime_eq_responses V a ha A J t ht]
    exact integral_const_mul _ _
  have hd := hasDerivAt_finiteStateGaussianTerminalCascade_outer_time V a ha A M J t ht H
  rw [hprior,hg,htmean] at hd
  convert hd using 1
  change (∫ y, finiteStateHessianTrace M U y-
    ∑ j ∈ Finset.range J, finiteStateCascadeCovarianceResponse V a L j (J-j) y (A j) ∂ν)/2 = _
  rw [integral_sub hiH hiS]
  ring

end FourPapersCommon
