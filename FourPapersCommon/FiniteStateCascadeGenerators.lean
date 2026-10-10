module
public import FourPapersCommon.FiniteStateGaussianCoordinateMeans
public import FourPapersCommon.FiniteStateSpectralTraces

@[expose] public section

/-! The actual parameter and variance generators written as expectations
under the normalized Gaussian transition used by the replica cascade. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
variable {S I : Type*} [Fintype S] [Fintype I]

theorem finiteStateGaussianInputMean_shift (a : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) (hF : Measurable F) (hG : Measurable G)
    (H : FiniteStateField S) :
    finiteStateGaussianInputMean a (fun z => F (H+L z)) (fun z => G (H+L z)) =
      ∫ y, G y ∂finiteStateGaussianStepLaw a L F H := by
  rw [finiteStateGaussianInputMean_eq_integral_tilted a _ _ (by fun_prop) (by fun_prop),
    finiteStateGaussianStepLaw_eq_map_tilted a L F hF H,
    integral_map (by fun_prop : Measurable (fun z => H+L z)).aemeasurable hG.aestronglyMeasurable]

theorem finiteStateGaussianVarianceGenerator_eq_stepLaw (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F : FiniteStateField S → ℝ) (hF : ContDiff ℝ 2 F) (H : FiniteStateField S) :
    finiteStateGaussianVarianceGenerator a v L F H =
      (∑ i, ∫ y, fderiv ℝ (fderiv ℝ F) y
          (L (finiteStateGaussianBasis I i)) (L (finiteStateGaussianBasis I i)) +
        a*(fderiv ℝ F y (L (finiteStateGaussianBasis I i)))^2
          ∂finiteStateGaussianStepLaw a (Real.sqrt v • L) F H)/2 := by
  have hDf : Continuous (fderiv ℝ F) := (hF.of_le (by norm_num) : ContDiff ℝ 1 F).continuous_fderiv (by norm_num)
  have hD : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hDD := hD.continuous_fderiv (by norm_num)
  unfold finiteStateGaussianVarianceGenerator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  let K := L (finiteStateGaussianBasis I i)
  have hg : Measurable (fun y => fderiv ℝ (fderiv ℝ F) y K K +
      a*(fderiv ℝ F y K)^2) :=
    (((hDD.clm_apply continuous_const).clm_apply continuous_const).add
      ((hDf.clm_apply continuous_const).pow 2 |>.const_mul a)).measurable
  exact pairedTiltMean_field_eq_stepLaw a v L F _ hF.continuous.measurable hg H

end FourPapersCommon
