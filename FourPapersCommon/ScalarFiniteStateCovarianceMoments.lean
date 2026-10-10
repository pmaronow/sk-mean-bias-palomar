module
public import FourPapersCommon.ScalarFiniteStatePairGamma
public import FourPapersCommon.FiniteStateCascadeTraceDecomposition

@[expose] public section

/-! Exact diagonal and split-copy moments for a scalar Gaussian covariance
direction. The split moment is the actual Brownian Γ, with no representation
or conditional-independence premise supplied by the caller. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000

@[simp] theorem scalarSpinAxis_apply (ε : Configuration 1) : scalarSpinAxis ε=spin (ε 0) := by
  simp [scalarSpinAxis,replicaSingleSiteSpinCLM,Fin.sum_univ_one,PiLp.single_apply]

theorem scalarSpinDirection_single (v : ℝ) :
    scalarSpinDirection v (EuclideanSpace.single (0 : Fin 1) 1)=Real.sqrt v • scalarSpinAxis := by
  dsimp only [scalarSpinDirection,ContinuousLinearMap.comp_apply,scalarSpinAxis]
  rw [←map_smul]
  congr 1

theorem scalarSpinDirection_spectral (v : ℝ) (hv : 0≤v) (ε ζ : Configuration 1) :
    finiteStateSpectralCovariance (scalarSpinDirection v) ε ζ=v*scalarSpinAxis ε*scalarSpinAxis ζ := by
  simp only [finiteStateSpectralCovariance,Fin.sum_univ_one,scalarSpinDirection_single,
    WithLp.ofLp_smul,Pi.smul_apply,smul_eq_mul]
  calc
    _=(Real.sqrt v)^2*(scalarSpinAxis ε*scalarSpinAxis ζ) := by ring
    _=_ := by rw [Real.sq_sqrt hv]; ring

theorem scalarGaussianCascade_diagonalMoment {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (J : ℕ) (v : ℝ) (hv : 0≤v) :
    finiteStateCascadeDiagonalMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) J 0 (finiteStateSpectralCovariance (scalarSpinDirection v))=v := by
  let _:=isMarkovKernel_finiteStateCascadeGibbsKernel (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) J
  unfold finiteStateCascadeDiagonalMoment
  simp_rw [scalarSpinDirection_spectral v hv,scalarSpinAxis_apply,mul_assoc,spin_mul_self,mul_one]
  simp

theorem scalarGaussianCascade_covarianceMoment_Gamma {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (p : ℕ) (hp : p≤k+2) (v : ℝ) (hv : 0≤v) :
    finiteStateCascadeCovarianceMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) p (k+2-p) 0 (finiteStateSpectralCovariance (scalarSpinDirection v))=
      v*mixedGamma (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) h
        (Paper.parisiSchemeMeasure s) (s.q (k+2-p)) := by
  unfold finiteStateCascadeCovarianceMoment
  simp_rw [scalarSpinDirection_spectral v hv]
  have he (z : Configuration 1×Configuration 1) :
      v*scalarSpinAxis z.1*scalarSpinAxis z.2=v*(scalarSpinAxis z.1*scalarSpinAxis z.2) := by ring
  simp_rw [he]
  rw [integral_const_mul,←finiteStateCascadePairMoment_eq_splitLaw (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) p (k+2-p) 0,
    scalarGaussianCascade_pairMoment_Gamma s β hβ h p hp]

/-- Identity-clock Γ at the normalized covariance time equals the literal
mixed Γ at the original physical overlap. -/
theorem mixedGamma_quadratic_clock (ξ : AdmissibleEvenMixture) (h : ℝ)
    (μ : Paper.ParisiMeasure) (q : ℝ) :
    mixedGamma (AdmissibleEvenMixture.quadratic ξ.variance ξ.variance_pos) h
      (mixedMeasure ξ μ) (ξ.clock q)=mixedGamma ξ h μ q := by
  unfold mixedGamma mixedState
  simp only [mixedGradient_quadratic,mixedMeasure_quadratic,
    AdmissibleEvenMixture.quadratic_clock,mixedBeta,AdmissibleEvenMixture.quadratic_variance,mixedGradient]

end FourPapersCommon
