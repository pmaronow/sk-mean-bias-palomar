module
public import FourPapersCommon.FiniteStateCascadeExpectations
public import OverlapPaper.ReplicaSourceGroupBaseline
public import OverlapPaper.ReplicaSourceHoeffding

@[expose] public section

/-! A bounded terminal source through the genuine normalized Gaussian
cascade. The coefficient is an expectation under its actual Gibbs law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]

theorem exp_finiteStateLogPartition_sub_eq_gibbsIntegral (V P : S → ℝ)
    (θ : ℝ) (H : FiniteStateField S) :
    Real.exp (gtStateLogPartition (fun σ => V σ + θ*P σ) H - gtStateLogPartition V H) =
      ∫ σ, Real.exp (θ*P σ) ∂finiteStateGibbsKernel V H := by
  rw [Real.exp_sub, gtStateLogPartition, gtStateLogPartition,
    Real.exp_log (gtStatePartition_pos _ _), Real.exp_log (gtStatePartition_pos _ _),
    integral_finiteStateGibbsKernel]
  simp only [gtStateGibbs, div_mul_eq_mul_div, ← Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [← Real.exp_add]
  congr 1
  ring

theorem finiteStateLogPartition_sub_eq_logAverage (V P : S → ℝ)
    (θ : ℝ) (H : FiniteStateField S) :
    gtStateLogPartition (fun σ => V σ + θ*P σ) H - gtStateLogPartition V H =
      sourceLogAverage (finiteStateGibbsKernel V H) 1 (fun σ => θ*P σ) := by
  rw [sourceLogAverage]
  simp only [one_ne_zero, ite_false, one_mul, div_one]
  rw [← exp_finiteStateLogPartition_sub_eq_gibbsIntegral, Real.log_exp]

theorem abs_finiteStateLogPartition_sub_le (V P : S → ℝ) (hP : ∀ σ, |P σ| ≤ 1)
    (θ : ℝ) (H : FiniteStateField S) :
    |gtStateLogPartition (fun σ => V σ + θ*P σ) H - gtStateLogPartition V H| ≤ |θ| := by
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  rw [finiteStateLogPartition_sub_eq_logAverage]
  apply sourceLogAverage_abs_le _ _ (measurable_of_finite _) |θ| (abs_nonneg θ) _ 1 zero_le_one
  intro σ
  rw [abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hP σ) (abs_nonneg θ)

theorem finiteStateGaussianTerminalCascade_sub_eq_sourceRecursion (V W : S → ℝ)
    (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascade W a L j H - finiteStateGaussianTerminalCascade V a L j H =
      sourceKernelRecursion (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V)) a j
        (fun y => gtStateLogPartition W y - gtStateLogPartition V y) H := by
  induction j generalizing H with
  | zero => rfl
  | succ j ih =>
    have hW := finiteStateGaussianTerminalCascade_lipschitz W a ha L j
    have hV := finiteStateGaussianTerminalCascade_lipschitz V a ha L j
    change finiteStateGaussianStep (a j) (L j) _ H - finiteStateGaussianStep (a j) (L j) _ H = _
    change sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) (a j)
      (fun z => finiteStateGaussianTerminalCascade W a L j (H+L j z)) -
      sourceLogAverage (stdGaussian (FiniteStateGaussianInput I)) (a j)
      (fun z => finiteStateGaussianTerminalCascade V a L j (H+L j z)) = _
    rw [sourceLogAverage_sub_tilted_all _ _ _ _
        (integrable_finiteStateGaussian_lipschitz _ hW _ _)
        (integrable_finiteStateGaussian_lipschitz _ hV _ _)
        (integrable_exp_finiteStateGaussian_lipschitz _ hW _ _ _)
        (integrable_exp_finiteStateGaussian_lipschitz _ hV _ _ _)]
    simp only [sourceKernelRecursion]
    rw [finiteStateGaussianCascadeKernel,
      finiteStateGaussianStepKernel_apply (a j) (L j)
        (finiteStateGaussianCascade a L (gtStateLogPartition V) j) hV.continuous.measurable,
      finiteStateGaussianStepLaw_eq_map_tilted (a j) (L j)
        (finiteStateGaussianCascade a L (gtStateLogPartition V) j) hV.continuous.measurable,
      sourceLogAverage_map
        ((stdGaussian (FiniteStateGaussianInput I)).tilted
          (fun z => a j * finiteStateGaussianCascade a L (gtStateLogPartition V) j (H+L j z)))
        (fun z : FiniteStateGaussianInput I => H+L j z) (by fun_prop) (a j)
        (sourceKernelRecursion (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V)) a j
          (fun y => gtStateLogPartition W y - gtStateLogPartition V y))
        (sourceKernelRecursion_measurable
          (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V)) a
          (fun y => gtStateLogPartition W y - gtStateLogPartition V y)
          (((contDiff_gtStateLogPartition W).continuous.sub
            (contDiff_gtStateLogPartition V).continuous).measurable) j)]
    congr 1
    funext z
    exact ih (H+L j z)

theorem finiteStateGaussianTerminalCascade_source_bound (V P : S → ℝ)
    (hP : ∀ σ, |P σ| ≤ 1) (θ : ℝ) (a : ℕ → ℝ) (ha : ∀ j, a j ∈ Icc 0 1)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) :
    finiteStateGaussianTerminalCascade (fun σ => V σ + θ*P σ) a L j H -
      finiteStateGaussianTerminalCascade V a L j H ≤
        θ*(∫ σ, P σ ∂finiteStateCascadeGibbsKernel V a L j H) + θ^2/2 := by
  have hQ := fun p => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a
    (fun p => (ha p).1) L p
  have hw : Measurable (fun y : FiniteStateField S =>
      gtStateLogPartition (fun σ => V σ+θ*P σ) y-gtStateLogPartition V y) :=
    ((contDiff_gtStateLogPartition _).continuous.sub (contDiff_gtStateLogPartition V).continuous).measurable
  rw [finiteStateGaussianTerminalCascade_sub_eq_sourceRecursion _ _ a (fun p => (ha p).1)]
  have hbound := sourceKernelRecursion_le_log_terminal_expectation _ hQ a ha _ hw |θ|
    (abs_nonneg θ) (abs_finiteStateLogPartition_sub_le V P hP θ) j H
  haveI := isMarkovKernel_finiteStateCascadeFieldKernel V a (fun p => (ha p).1) L j
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a (fun p => (ha p).1) L j
  haveI := isMarkovKernel_finiteStateGibbsKernel V
  have hrewrite : (∫ y, Real.exp (gtStateLogPartition (fun σ => V σ+θ*P σ) y-
      gtStateLogPartition V y) ∂finiteStateCascadeFieldKernel V a L j H) =
      ∫ σ, Real.exp (θ*P σ) ∂finiteStateCascadeGibbsKernel V a L j H := by
    simp_rw [exp_finiteStateLogPartition_sub_eq_gibbsIntegral]
    rw [finiteStateCascadeGibbsKernel, Kernel.integral_comp
      (source_bounded_exp_integrable _ P (measurable_of_finite _) 1 hP θ)]
  change _ ≤ Real.log (∫ y, Real.exp _ ∂finiteStateCascadeFieldKernel V a L j H) at hbound
  rw [hrewrite] at hbound
  exact hbound.trans (source_log_mgf_le _ P (measurable_of_finite _).aemeasurable
    (Filter.Eventually.of_forall hP) θ)

end FourPapersCommon
