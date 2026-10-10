module
public import FourPapersCommon.GenericFiniteStateCascadeParameter
public import FourPapersCommon.FiniteStateCascadeKernels

@[expose] public section

/-! The coordinate tilted means used in the actual Gaussian differentiation
theorems are expectations under the genuine normalized Gaussian laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
variable {S I : Type*} [Fintype S] [Fintype I]

private theorem integral_gaussian_coordinates (g : FiniteStateGaussianInput I → ℝ)
    (hg : Measurable g) :
    (∫ z, g z ∂stdGaussian (FiniteStateGaussianInput I)) =
      ∫ y, g (∑ i, y i • finiteStateGaussianBasis I i)
        ∂SpinGlass.Targets.piGauss (Fintype.card I) := by
  rw [stdGaussian_eq_map_pi_orthonormalBasis (finiteStateGaussianBasis I)]
  exact integral_map (Measurable.aemeasurable (by fun_prop)) hg.aestronglyMeasurable

theorem pairedTiltMean_field_eq_stepLaw (a v : ℝ)
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (F G : FiniteStateField S → ℝ) (hF : Measurable F) (hG : Measurable G)
    (H : FiniteStateField S) :
    SpinGlass.Targets.pairedTiltMean a v
      (fun y => F (H+finiteStateGaussianCoordinateField L y))
      (fun y => G (H+finiteStateGaussianCoordinateField L y)) 0 =
        ∫ y, G y ∂finiteStateGaussianStepLaw a (Real.sqrt v • L) F H := by
  have heq (y : Fin (Fintype.card I) → ℝ) :
      H+(Real.sqrt v • L) (∑ i, y i • finiteStateGaussianBasis I i) =
      H+finiteStateGaussianCoordinateField L (fun i => Real.sqrt v*y i) := by
    simp only [smul_apply, map_sum, map_smul, finiteStateGaussianCoordinateField_apply,
      smul_smul, mul_comm]
  rw [finiteStateGaussianStepLaw_eq_map_tilted a _ F hF H,
    integral_map (by fun_prop : Measurable (fun z => H+(Real.sqrt v • L) z)).aemeasurable
      hG.aestronglyMeasurable, integral_tilted]
  rw [integral_gaussian_coordinates _ (by fun_prop),
    integral_gaussian_coordinates _ (by fun_prop)]
  simp only [heq, SpinGlass.Targets.pairedTiltMean, SpinGlass.Targets.tiltWeightPi,
    Pi.zero_apply, zero_add, smul_eq_mul]
  by_cases ha : a = 0
  · simp [ha]
  · simp only [ha, ite_false]
    congr 1
    funext y
    ring

theorem finiteStateGaussianInputMean_eq_integral_tilted (a : ℝ)
    (F D : FiniteStateGaussianInput I → ℝ) (hF : Measurable F) (hD : Measurable D) :
    finiteStateGaussianInputMean a F D =
      ∫ z, D z ∂(stdGaussian (FiniteStateGaussianInput I)).tilted (fun z => a*F z) := by
  have hh := pairedTiltMean_field_eq_stepLaw a 1
    (ContinuousLinearMap.id ℝ (FiniteStateGaussianInput I)) F D hF hD 0
  simpa only [finiteStateGaussianInputMean, Real.sqrt_one, one_smul, zero_add,
    ContinuousLinearMap.id_apply, finiteStateGaussianStepLaw, finiteStateGaussianRawKernel_apply,
    Measure.map_id'] using hh

end FourPapersCommon
