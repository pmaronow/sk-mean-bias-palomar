module
public import FourPapersCommon.FiniteStateCascadeHessianTelescoping

@[expose] public section

/-! Covariance contractions of the exact Hessian decomposition, written
entirely under the genuine terminal Gibbs and split-replica probability laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass.AT
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J] [DecidableEq J]
  [MeasurableSpace S] [MeasurableSingletonClass S] [Nonempty S]
set_option maxHeartbeats 1400000

def finiteStateCascadeDiagonalMoment (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S) (C : S → S → ℝ) : ℝ :=
  ∫ σ, C σ σ ∂finiteStateCascadeGibbsKernel V a L j H

def finiteStateCascadeCovarianceMoment (V : S → ℝ) (a : ℕ → ℝ)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H : FiniteStateField S) (C : S → S → ℝ) : ℝ :=
  ∫ z, C z.1 z.2 ∂finiteStateCascadeSplitLaw V a L p q H

theorem finiteStateCascadeDiagonalMoment_spectral (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateCascadeDiagonalMoment V a L j H (finiteStateSpectralCovariance A) =
      ∑ i : J, fderiv ℝ (finiteStateGaussianTerminalCascade V a L j) H
        (finiteStatePointwiseProduct (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single i 1))) := by
  haveI := isMarkovKernel_finiteStateCascadeGibbsKernel V a ha L j
  unfold finiteStateCascadeDiagonalMoment finiteStateSpectralCovariance
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_finiteStateGaussianTerminalCascade_eq_gibbsMean V a ha L j]
  rfl

theorem finiteStateCascadeCovarianceMoment_spectral (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (p q : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateCascadeCovarianceMoment V a L p q H (finiteStateSpectralCovariance A) =
      ∑ i : J, finiteStateCascadePairMoment V a L p q H
        (A (EuclideanSpace.single i 1)) (A (EuclideanSpace.single i 1)) := by
  haveI := isProbabilityMeasure_finiteStateCascadeSplitLaw V a ha L p q H
  unfold finiteStateCascadeCovarianceMoment finiteStateSpectralCovariance
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  apply Finset.sum_congr rfl
  intro i _
  exact (finiteStateCascadePairMoment_eq_splitLaw V a ha L p q H _ _).symm

theorem finiteStateCascadeHessian_trace_decomposition (V : S → ℝ) (a : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (j : ℕ) (H : FiniteStateField S)
    (A : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S) :
    finiteStateHessianTrace A (finiteStateGaussianTerminalCascade V a L j) H +
      a j * finiteStateGradientSquareTrace A (finiteStateGaussianTerminalCascade V a L j) H =
      finiteStateCascadeDiagonalMoment V a L j H (finiteStateSpectralCovariance A) +
      (a 0-1)*finiteStateCascadeCovarianceMoment V a L 0 j H (finiteStateSpectralCovariance A) +
      ∑ p ∈ Finset.range j, (a (p+1)-a p) *
        finiteStateCascadeCovarianceMoment V a L (p+1) (j-(p+1)) H (finiteStateSpectralCovariance A) := by
  rw [finiteStateCascadeDiagonalMoment_spectral V a ha L,
    finiteStateCascadeCovarianceMoment_spectral V a ha L]
  simp_rw [finiteStateCascadeCovarianceMoment_spectral V a ha L]
  unfold finiteStateHessianTrace finiteStateGradientSquareTrace
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  simp_rw [pow_two, ← mul_assoc,
    finiteStateCascadeHessian_pair_decomposition V a ha L j H]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_comm]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.mul_sum]

end FourPapersCommon
