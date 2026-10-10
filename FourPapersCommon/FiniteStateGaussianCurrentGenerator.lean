module
public import FourPapersCommon.GenericFiniteStateCascadeGeneratorMean
public import FourPapersCommon.FiniteStateCascadeGenerators

@[expose] public section

/-! The variance generator of a genuine Gaussian step is its spatial generator
at the current potential.  The Hessian covariance correction cancels against
the current gradient-square term. -/

noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped ContDiff NNReal BigOperators

namespace FourPapersCommon

variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianVarianceGenerator_eq_currentGenerator
    (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B)
    (H : FiniteStateField S) :
    finiteStateGaussianVarianceGenerator a v L F H =
      finiteStateGaussianGeneratorField a L
        (finiteStateGaussianStep a (Real.sqrt v • L) F) H := by
  classical
  have hF1 : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hfirst : fderiv ℝ (finiteStateGaussianStep a (Real.sqrt v • L) F) =
      finiteStateGaussianDifferential a (Real.sqrt v • L) F :=
    funext fun y =>
      (hasFDerivAt_finiteStateGaussianStep a (Real.sqrt v • L) F hF1 C hC y).fderiv
  have hsecond :
      fderiv ℝ (fderiv ℝ (finiteStateGaussianStep a (Real.sqrt v • L) F)) H =
        finiteStateGaussianHessian a (Real.sqrt v • L) F H := by
    rw [hfirst]
    exact (hasFDerivAt_finiteStateGaussianDifferential a (Real.sqrt v • L)
      F hF C B hC hB H).fderiv
  rw [finiteStateGaussianVarianceGenerator_eq_stepLaw a v L F hF H,
    finiteStateGaussianGeneratorField]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hsecond, hfirst,
    finiteStateGaussianHessian_apply_eq_integral a (Real.sqrt v • L)
      F hF C B hC hB H]
  have he :
      (fun y : FiniteStateField S =>
        fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i))
          (L (finiteStateGaussianBasis I i)) +
        a * fderiv ℝ F y (L (finiteStateGaussianBasis I i)) *
          fderiv ℝ F y (L (finiteStateGaussianBasis I i))) =
      (fun y : FiniteStateField S =>
        fderiv ℝ (fderiv ℝ F) y (L (finiteStateGaussianBasis I i))
          (L (finiteStateGaussianBasis I i)) +
        a * (fderiv ℝ F y (L (finiteStateGaussianBasis I i))) ^ 2) := by
    funext y
    ring
  rw [he]
  ring

theorem hasDerivAt_finiteStateGaussianStep_variance_currentGenerator
    (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F)
    (C B : ℝ≥0) (hC : ∀ H, ‖fderiv ℝ F H‖ ≤ C)
    (hB : ∀ H, ‖fderiv ℝ (fderiv ℝ F) H‖ ≤ B)
    (H : FiniteStateField S) {v : ℝ} (hv : 0 < v) :
    HasDerivAt (fun w => finiteStateGaussianStep a (Real.sqrt w • L) F H)
      (finiteStateGaussianGeneratorField a L
        (finiteStateGaussianStep a (Real.sqrt v • L) F) H) v := by
  rw [← finiteStateGaussianVarianceGenerator_eq_currentGenerator
    a v L F hF C B hC hB H]
  exact hasDerivAt_finiteStateGaussianStep_variance a L F hF C B hC hB H hv

end FourPapersCommon
