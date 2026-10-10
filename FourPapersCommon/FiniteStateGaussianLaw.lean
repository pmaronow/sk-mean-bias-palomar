module
public import FourPapersCommon.FiniteStateCascadeDefinitions
public import FourPapersCommon.FiniteStateSpectralTraces
public import OverlapPaper.ReplicaSourceSpectralCovariance
public import Mathlib.Probability.Distributions.Gaussian.CharFun

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Gaussian realization invariance of a finite-state cascade step. Equal
finite spectral covariance gives equal actual centered Gaussian field laws,
even when their driving Gaussian spaces have different dimensions. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace FourPapersCommon
variable {S I J : Type*} [Fintype S] [Fintype I] [Fintype J]
  [DecidableEq S] [DecidableEq I] [DecidableEq J]
set_option maxHeartbeats 1200000

theorem stdGaussian_map_eq_of_spectral_covariance
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (hcov : ∀ σ τ, finiteStateSpectralCovariance L σ τ = finiteStateSpectralCovariance M σ τ) :
    (stdGaussian (FiniteStateGaussianInput I)).map L =
      (stdGaussian (FiniteStateGaussianInput J)).map M := by
  apply IsGaussian.ext
  · change (∫ x, x ∂(stdGaussian (FiniteStateGaussianInput I)).map L) =
      ∫ x, x ∂(stdGaussian (FiniteStateGaussianInput J)).map M
    rw [L.integral_id_map IsGaussian.integrable_id, M.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian, integral_id_stdGaussian, map_zero, map_zero]
  · apply (ContinuousLinearMap.toBilinForm_inj _ _).mp
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun S ℝ).toBasis
    intro σ τ
    simp only [ContinuousLinearMap.toBilinForm_apply, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
    change covarianceBilin ((stdGaussian (FiniteStateGaussianInput I)).map L)
      (EuclideanSpace.single σ 1) (EuclideanSpace.single τ 1) =
      covarianceBilin ((stdGaussian (FiniteStateGaussianInput J)).map M)
        (EuclideanSpace.single σ 1) (EuclideanSpace.single τ 1)
    rw [covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covariance_map (by fun_prop) (by fun_prop) L.measurable.aemeasurable,
      covariance_map (by fun_prop) (by fun_prop) M.measurable.aemeasurable]
    simp only [Function.comp_def, EuclideanSpace.inner_single_left, map_one, one_mul]
    change cov[(EuclideanSpace.proj σ).comp L, (EuclideanSpace.proj τ).comp L;
      stdGaussian (FiniteStateGaussianInput I)] =
      cov[(EuclideanSpace.proj σ).comp M, (EuclideanSpace.proj τ).comp M;
        stdGaussian (FiniteStateGaussianInput J)]
    rw [OverlapPaper.source_stdGaussian_covariance_trace, OverlapPaper.source_stdGaussian_covariance_trace]
    exact hcov σ τ

theorem finiteStateGaussianRawKernel_eq_of_spectral_covariance
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (hcov : ∀ σ τ, finiteStateSpectralCovariance L σ τ = finiteStateSpectralCovariance M σ τ)
    (H : FiniteStateField S) : finiteStateGaussianRawKernel L H = finiteStateGaussianRawKernel M H := by
  rw [finiteStateGaussianRawKernel_apply, finiteStateGaussianRawKernel_apply]
  have hl : (fun z => H+L z) = (fun y : FiniteStateField S => H+y) ∘ L := rfl
  have hm : (fun z => H+M z) = (fun y : FiniteStateField S => H+y) ∘ M := rfl
  rw [hl, hm, ← Measure.map_map (by fun_prop) L.measurable,
    ← Measure.map_map (by fun_prop) M.measurable,
    stdGaussian_map_eq_of_spectral_covariance L M hcov]

theorem finiteStateGaussianStepLaw_eq_of_spectral_covariance
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (hcov : ∀ σ τ, finiteStateSpectralCovariance L σ τ = finiteStateSpectralCovariance M σ τ)
    (a : ℝ) (F : FiniteStateField S → ℝ) (H : FiniteStateField S) :
    finiteStateGaussianStepLaw a L F H = finiteStateGaussianStepLaw a M F H := by
  rw [finiteStateGaussianStepLaw, finiteStateGaussianStepLaw,
    finiteStateGaussianRawKernel_eq_of_spectral_covariance L M hcov H]

theorem finiteStateGaussianStep_eq_of_spectral_covariance
    (L : FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (M : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (hcov : ∀ σ τ, finiteStateSpectralCovariance L σ τ = finiteStateSpectralCovariance M σ τ)
    (a : ℝ) (F : FiniteStateField S → ℝ) (hF : Measurable F) (H : FiniteStateField S) :
    finiteStateGaussianStep a L F H = finiteStateGaussianStep a M F H := by
  have hmean : (∫ z, F (H+L z) ∂stdGaussian (FiniteStateGaussianInput I)) =
      ∫ z, F (H+M z) ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [← integral_map (by fun_prop : Measurable (fun z => H+L z)).aemeasurable hF.aestronglyMeasurable,
      ← integral_map (by fun_prop : Measurable (fun z => H+M z)).aemeasurable hF.aestronglyMeasurable]
    rw [← finiteStateGaussianRawKernel_apply, ← finiteStateGaussianRawKernel_apply,
      finiteStateGaussianRawKernel_eq_of_spectral_covariance L M hcov H]
  have hexp : (∫ z, Real.exp (a*F (H+L z)) ∂stdGaussian (FiniteStateGaussianInput I)) =
      ∫ z, Real.exp (a*F (H+M z)) ∂stdGaussian (FiniteStateGaussianInput J) := by
    rw [← integral_map (by fun_prop : Measurable (fun z => H+L z)).aemeasurable (hF.const_mul a).exp.aestronglyMeasurable,
      ← integral_map (by fun_prop : Measurable (fun z => H+M z)).aemeasurable (hF.const_mul a).exp.aestronglyMeasurable]
    rw [← finiteStateGaussianRawKernel_apply, ← finiteStateGaussianRawKernel_apply,
      finiteStateGaussianRawKernel_eq_of_spectral_covariance L M hcov H]
  unfold finiteStateGaussianStep OverlapPaper.sourceLogAverage
  split_ifs <;> simp only [hmean, hexp]

end FourPapersCommon
