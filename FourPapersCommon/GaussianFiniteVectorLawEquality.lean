module
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Probability.Moments.CovarianceBilin

public import Mathlib.Probability.Distributions.Gaussian.Fernique

@[expose] public section

/-! Genuine finite Gaussian vector laws are determined by their actual
coordinate means and covariances. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
namespace FourPapersCommon

theorem gaussian_finite_vector_law_eq_of_mean_covariance
    {Ω Ω' J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [Fintype J]
    (P : Measure Ω) (Q : Measure Ω')
    (X : Ω→EuclideanSpace ℝ J) (Y : Ω'→EuclideanSpace ℝ J)
    (hX : HasGaussianLaw X P) (hY : HasGaussianLaw Y Q)
    (hmean : ∀j,(∫ω,X ω j ∂P)=(∫ω,Y ω j ∂Q))
    (hcov : ∀i j,cov[fun ω=>X ω i,fun ω=>X ω j;P]=
      cov[fun ω=>Y ω i,fun ω=>Y ω j;Q]) :
    P.map X=Q.map Y := by
  haveI := hX.isProbabilityMeasure
  haveI := hY.isProbabilityMeasure
  haveI := hX.isGaussian_map
  haveI := hY.isGaussian_map
  apply IsGaussian.ext
  · rw [integral_map hX.aemeasurable aestronglyMeasurable_id,
      integral_map hY.aemeasurable aestronglyMeasurable_id]
    ext j
    have hx := (EuclideanSpace.proj j).integral_comp_comm hX.integrable
    have hy := (EuclideanSpace.proj j).integral_comp_comm hY.integrable
    exact hx.symm.trans ((hmean j).trans hy)
  · rw [←ContinuousLinearMap.toBilinForm_inj]
    apply LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
    intro i j
    rw [ContinuousLinearMap.toBilinForm_apply,ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov,covarianceBilin_apply_eq_cov]
    · rw [covariance_map_fun (by fun_prop) (by fun_prop) hX.aemeasurable,
        covariance_map_fun (by fun_prop) (by fun_prop) hY.aemeasurable]
      simpa only [OrthonormalBasis.coe_toBasis,EuclideanSpace.basisFun_inner] using hcov i j
    all_goals exact IsGaussian.memLp_two_id

end FourPapersCommon
