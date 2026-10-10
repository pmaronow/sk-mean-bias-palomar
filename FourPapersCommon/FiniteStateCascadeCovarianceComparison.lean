module
public import FourPapersCommon.FiniteStateCascadeConvexity

@[expose] public section

/-! Genuine Hessian/covariance comparison for a finite Gaussian cascade.
The covariance is the variance of a terminal observable under the actual
composed Gibbs kernel. Its conditional-variance recurrence is proved from
the normalized first derivative, including zero mass and singular inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators ContDiff
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I : Type*} [Fintype S] [Fintype I] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
set_option maxHeartbeats 1800000

def finiteStateCascadeObservableVariance (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) : ℝ :=
  fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H (finiteStatePointwiseProduct K K) -
    (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H K)^2

theorem finiteStateCascadeObservableVariance_eq_variance (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    finiteStateCascadeObservableVariance V a L j H K =
      variance (fun σ : S => K σ) (finiteStateCascadeGibbsKernel V a L j H) := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  have hk : MemLp (fun σ : S => K σ) 2 (finiteStateCascadeGibbsKernel V a L j H) := by
    exact (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).mpr
      Integrable.of_finite
  rw [finiteStateCascadeObservableVariance,variance_eq_sub hk,
    fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j H,
    fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j H]
  simp only [finiteStatePointwiseProduct_apply,Pi.pow_apply,pow_two]

theorem finiteStateCascadeObservableVariance_nonneg (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    0 ≤ finiteStateCascadeObservableVariance V a L j H K := by
  rw [finiteStateCascadeObservableVariance_eq_variance V a ha L j H K]
  exact variance_nonneg _ _

theorem continuous_finiteStateCascadeObservableVariance (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (K : FiniteStateField S) :
    Continuous (fun H => finiteStateCascadeObservableVariance V a L j H K) := by
  have hd := (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous_fderiv (by norm_num)
  exact (hd.clm_apply continuous_const).sub ((hd.clm_apply continuous_const).pow 2)

theorem finiteStateCascadeObservableVariance_abs_le (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    |finiteStateCascadeObservableVariance V a L j H K| ≤
      ‖finiteStatePointwiseProduct K K‖ + ‖K‖^2 := by
  apply (abs_sub _ _).trans
  apply add_le_add (finiteStateCascadeFirst_abs_le V a ha L j H _)
  rw [abs_sq]
  have hb := finiteStateCascadeFirst_abs_le V a ha L j H K
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2

theorem integrable_finiteStateCascadeObservableVariance (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (K : FiniteStateField S)
    (P : Measure (FiniteStateField S)) [IsProbabilityMeasure P] :
    Integrable (fun H => finiteStateCascadeObservableVariance V a L j H K) P :=
  source_bounded_integrable _ _ (continuous_finiteStateCascadeObservableVariance V a ha L j K).measurable _
    (fun H => finiteStateCascadeObservableVariance_abs_le V a ha L j H K)

theorem finiteStateCascadeObservableVariance_succ (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    finiteStateCascadeObservableVariance V a L (j+1) H K =
      (∫ y, finiteStateCascadeObservableVariance V a L j y K
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) +
      variance (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K)
        (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) := by
  let P := finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H
  haveI : IsProbabilityMeasure P := by
    dsimp [P]; haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
    infer_instance
  have hg := ((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous_fderiv
    (by norm_num)).clm_apply (continuous_const (y := K))
  have hgLp : MemLp (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K) 2 P :=
    memLp_of_bounded (.of_forall fun y => abs_le.mp (finiteStateCascadeFirst_abs_le V a ha L j y K))
      hg.measurable.aestronglyMeasurable 2
  have hi := integrable_finiteStateCascadeFirst_kernel V a ha L j j H (finiteStatePointwiseProduct K K)
  unfold finiteStateCascadeObservableVariance
  rw [integral_sub hi hgLp.integrable_sq,variance_eq_sub hgLp,
    fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H,
    fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H]
  simp only [Pi.pow_apply]
  ring

theorem finiteStateCascadeHessian_succ_variance (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L (j+1))) H K K =
      (∫ y, fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K
        ∂finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) +
      a j * variance (fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K)
        (finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H) := by
  let P := finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H
  let g := fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K
  let d := fun y => fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K
  haveI : IsProbabilityMeasure P := by
    dsimp [P]; haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
    infer_instance
  have hc := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
  have hg := (hc.1.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := K))
  have hgLp : MemLp g 2 P :=
    memLp_of_bounded (.of_forall fun y => abs_le.mp (finiteStateCascadeFirst_abs_le V a ha L j y K))
      hg.measurable.aestronglyMeasurable 2
  have hcD : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) := hc.1.fderiv_right (by norm_num)
  have hd := (hcD.continuous_fderiv (by norm_num)).clm_apply
    (continuous_const (y := K)) |>.clm_apply (continuous_const (y := K))
  have hdB (y : FiniteStateField S) : |d y| ≤ finiteStateCascadeHessianBound a j * ‖K‖ * ‖K‖ := by
    have h1 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y).le_opNorm K
    have h2 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K).le_opNorm K
    rw [Real.norm_eq_abs] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right
      (h1.trans (mul_le_mul_of_nonneg_right (hc.2 y) (norm_nonneg K))) (norm_nonneg K))
  have hdInt : Integrable d P := source_bounded_integrable _ _ hd.measurable _ hdB
  have hEq : (∫ y, d y + a j*g y*g y ∂P) = (∫ y, d y ∂P) + a j*∫ y, g y^2 ∂P := by
    simp_rw [show ∀ y, a j*g y*g y=a j*g y^2 by intro y; ring]
    rw [integral_add hdInt (hgLp.integrable_sq.const_mul _),integral_const_mul]
  rw [second_fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H K K]
  change (∫ y, d y+a j*g y*g y ∂P)-a j*_*_ = _
  rw [hEq,fderiv_finiteStateGaussianTerminalCascade_succ_integral V a ha L j H K,
    variance_eq_sub hgLp]
  simp only [Pi.pow_apply]
  ring

def finiteStateCascadeDepthMass (a : ℕ → ℝ) (j : ℕ) : ℝ := if j=0 then 1 else a (j-1)

theorem finiteStateCascadeHessian_covariance_bounds (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (ha1 : ∀ j, a j ≤ 1) (hdec : ∀ j, a (j+1) ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H K : FiniteStateField S) :
    finiteStateCascadeDepthMass a j * finiteStateCascadeObservableVariance V a L j H K ≤
      fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K ∧
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) H K K ≤
      finiteStateCascadeObservableVariance V a L j H K := by
  induction j generalizing H with
  | zero =>
    have he : fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L 0)) H K K =
        finiteStateCascadeObservableVariance V a L 0 H K := by
      rw [finiteStateCascadeObservableVariance_eq_variance V a ha L 0 H K]
      change fderiv ℝ (fderiv ℝ (gtStateLogPartition V)) H K K = _
      rw [second_fderiv_finiteStateTerminal_eq_gibbsCovariance]
      haveI := isMarkovKernel_finiteStateGibbsKernel V
      have hk : MemLp (fun σ : S => K σ) 2 (finiteStateGibbsKernel V H) :=
        (memLp_two_iff_integrable_sq (measurable_of_finite _).aestronglyMeasurable).mpr Integrable.of_finite
      simp only [finiteStateCascadeGibbsKernel,finiteStateCascadeFieldKernel,sourceKernelLaw,Kernel.comp_id]
      rw [variance_eq_sub hk]
      simp only [Pi.pow_apply,pow_two]
    rw [he]; simp [finiteStateCascadeDepthMass]
  | succ j ih =>
    let P := finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) j H
    haveI : IsProbabilityMeasure P := by
      dsimp [P]; haveI := isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L j
      infer_instance
    have hiC := integrable_finiteStateCascadeObservableVariance V a ha L j K P
    have hiH : Integrable (fun y => fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K) P := by
      have hc := finiteStateGaussianTerminalCascade_C2_bounds V a ha L j
      have hcd : ContDiff ℝ 1 (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) := hc.1.fderiv_right (by norm_num)
      have hd := (hcd.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const (y := K)) |>.clm_apply (continuous_const (y := K))
      apply source_bounded_integrable _ _ hd.measurable (finiteStateCascadeHessianBound a j*‖K‖*‖K‖)
      intro y
      have h1 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y).le_opNorm K
      have h2 := (fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K).le_opNorm K
      rw [Real.norm_eq_abs] at h2
      exact h2.trans (mul_le_mul_of_nonneg_right
        (h1.trans (mul_le_mul_of_nonneg_right (hc.2 y) (norm_nonneg K))) (norm_nonneg K))
    have hm : a j ≤ finiteStateCascadeDepthMass a j := by
      cases j with
      | zero => simpa [finiteStateCascadeDepthMass] using ha1 0
      | succ j => simpa [finiteStateCascadeDepthMass] using hdec j
    have hl := integral_mono (hiC.const_mul (a j)) hiH (fun y =>
      (mul_le_mul_of_nonneg_right hm (finiteStateCascadeObservableVariance_nonneg V a ha L j y K)).trans (ih y).1)
    have hr := integral_mono hiH hiC (fun y => (ih y).2)
    rw [integral_const_mul] at hl
    rw [finiteStateCascadeObservableVariance_succ V a ha L j H K,
      finiteStateCascadeHessian_succ_variance V a ha L j H K]
    have hv := variance_nonneg (X := fun y => fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y K) (μ := P)
    have hmv := mul_le_mul_of_nonneg_right (ha1 j) hv
    simp only [finiteStateCascadeDepthMass,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel]
    change a j*((∫ y, finiteStateCascadeObservableVariance V a L j y K ∂P)+_) ≤
      (∫ y, fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y K K ∂P)+_ ∧ _
    constructor <;> nlinarith

end FourPapersCommon
