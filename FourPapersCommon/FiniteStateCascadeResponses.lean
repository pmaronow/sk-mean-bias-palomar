module
public import FourPapersCommon.FiniteStateCascadePropagation
public import FourPapersCommon.FiniteStateCascadeTraceDecomposition

@[expose] public section

/-! Genuine normalized covariance response of each Gaussian cascade layer,
propagated through its outer layers, and the exact split-law formula. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J] [DecidableEq J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1600000

def finiteStateCascadeCovarianceResponse (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) : ℝ :=
  ∑ i : J, sourceKernelExpectation
    (fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)) q
    (fun y => fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade V a L j)) y
      (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single i 1)) +
      a j * fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y (A (EuclideanSpace.single i 1)) *
        fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) y (A (EuclideanSpace.single i 1))) H

theorem finiteStateCascadeCovarianceResponse_eq_split_moments (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L j q H A =
      finiteStateCascadeDiagonalMoment V a L (j+q) H (finiteStateSpectralCovariance A) +
      (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 (j+q) H (finiteStateSpectralCovariance A) +
      ∑ p ∈ Finset.range j, (a (p+1)-a p)*
        finiteStateCascadeCovarianceMoment V a L (p+1) ((j+q)-(p+1)) H (finiteStateSpectralCovariance A) := by
  rw [finiteStateCascadeDiagonalMoment_spectral V a ha L,
    finiteStateCascadeCovarianceMoment_spectral V a ha L]
  simp_rw [finiteStateCascadeCovarianceMoment_spectral V a ha L]
  unfold finiteStateCascadeCovarianceResponse
  simp_rw [finiteStateCascadeHessian_propagated_pair_decomposition V a ha L j q H]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]

theorem finiteStateCascadeCovarianceResponse_eq_kernelExpectation (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j q : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateCascadeCovarianceResponse V a L j q H A =
      sourceKernelExpectation
        (fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)) q
        (fun y => finiteStateHessianTrace A (finiteStateGaussianTerminalCascade V a L j) y +
          a j * finiteStateGradientSquareTrace A (finiteStateGaussianTerminalCascade V a L j) y) H := by
  classical
  let U := finiteStateGaussianTerminalCascade V a L j
  let b := fun i y => fderiv ℝ (fderiv ℝ U) y (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single i 1)) +
    a j * fderiv ℝ U y (A (EuclideanSpace.single i 1)) * fderiv ℝ U y (A (EuclideanSpace.single i 1))
  let C := fun i => ((finiteStateCascadeHessianBound a j : ℝ)+|a j|)*‖A (EuclideanSpace.single i 1)‖^2
  have hu : ContDiff ℝ 2 U := contDiff_two_finiteStateGaussianTerminalCascade V a ha L j
  have hD : ContDiff ℝ 1 (fderiv ℝ U) := hu.fderiv_right (by norm_num)
  have h1 := (hu.of_le (by norm_num) : ContDiff ℝ 1 U).continuous_fderiv (by norm_num)
  have h2 := hD.continuous_fderiv (by norm_num)
  have hbm (i : J) : Measurable (b i) :=
    (((h2.clm_apply continuous_const).clm_apply continuous_const).add
      (((h1.clm_apply continuous_const).const_mul (a j)).mul (h1.clm_apply continuous_const))).measurable
  have hcb (i : J) : 0 ≤ C i := by dsimp [C]; positivity
  have hbb (i : J) (y : FiniteStateField S) : |b i y| ≤ C i := by
    let K := A (EuclideanSpace.single i 1)
    have hgrad := finiteStateCascadeFirst_abs_le V a ha L j y K
    have hB := (finiteStateGaussianTerminalCascade_C2_bounds V a ha L j).2 y
    have hb1 := (fderiv ℝ (fderiv ℝ U) y).le_opNorm K
    have hb2 := (fderiv ℝ (fderiv ℝ U) y K).le_opNorm K
    rw [Real.norm_eq_abs] at hb2
    have hb : |fderiv ℝ (fderiv ℝ U) y K K| ≤
        (finiteStateCascadeHessianBound a j : ℝ)*‖K‖^2 := by
      have hstep := mul_le_mul_of_nonneg_right (hb1.trans
        (mul_le_mul_of_nonneg_right hB (norm_nonneg K))) (norm_nonneg K)
      exact hb2.trans (by simpa only [pow_two, mul_assoc] using hstep)
    have hg : |a j * fderiv ℝ U y K * fderiv ℝ U y K| ≤ |a j| *‖K‖^2 := by
      simp only [abs_mul]
      have hp := mul_le_mul hgrad hgrad (abs_nonneg _) (norm_nonneg K)
      calc
        _ = |a j| *(|fderiv ℝ U y K| *|fderiv ℝ U y K|) := by ring
        _ ≤ |a j| *(‖K‖*‖K‖) := mul_le_mul_of_nonneg_left hp (abs_nonneg _)
        _ = _ := by ring
    exact (abs_add_le _ _).trans (by dsimp [C]; nlinarith [hb, hg])
  have he := sourceKernelExpectation_finsetSum (Finset.univ : Finset J)
    (fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p))
    (fun p => isMarkovKernel_finiteStateGaussianTerminalCascadeKernel V a ha L (j+p)) b
    (fun i _ => hbm i) C (fun i _ => hcb i) (fun i _ => hbb i) q H
  change (∑ i : J, sourceKernelExpectation
    (fun p => finiteStateGaussianCascadeKernel a L (gtStateLogPartition V) (j+p)) q (b i) H) = _
  rw [← he]
  congr 2
  funext y
  dsimp [b]
  unfold finiteStateHessianTrace finiteStateGradientSquareTrace
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

end FourPapersCommon
