module
public import FourPapersCommon.ScalarFiniteStateCovarianceMoments
public import FourPapersCommon.FiniteStateCascadeResponses

@[expose] public section

/-! The exact normalized covariance response of a scalar scheme, in terms
of its actual Brownian Γ at the mass-drop nodes. This is a genuine Gaussian
response identity, not a proposed coefficient derivative supplied as input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace FourPapersCommon
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT
set_option maxHeartbeats 1800000

theorem scalarGaussianCascade_response_Gamma {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : 0<β) (h : ℝ) (j : ℕ) (hj : j<k+2) (v : ℝ) (hv : 0≤v) :
    finiteStateCascadeCovarianceResponse (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) j (k+2-j) 0 (scalarSpinDirection v)=
      v*(1+∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
        mixedGamma (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) h
          (Paper.parisiSchemeMeasure s) (s.q (k+2-(p+1)))) := by
  rw [finiteStateCascadeCovarianceResponse_eq_split_moments (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s)]
  rw [show j+(k+2-j)=k+2 by omega,scalarGaussianCascade_diagonalMoment s β h _ v hv]
  have hm : scalarSchemeMass s 0=1 := by simp [scalarSchemeMass,s.m_top]
  rw [hm,sub_self,zero_mul,add_zero]
  have he : (∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
      finiteStateCascadeCovarianceMoment (scalarSpinPotential h) (scalarSchemeMass s)
        (scalarSchemeSpinInput s β) (p+1) (k+2-(p+1)) 0 (finiteStateSpectralCovariance (scalarSpinDirection v)))=
      v*∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
        mixedGamma (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ)) h
          (Paper.parisiSchemeMeasure s) (s.q (k+2-(p+1))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [scalarGaussianCascade_covarianceMoment_Gamma s β hβ h (p+1) (by
      have hpj:=Finset.mem_range.mp hp
      omega) v hv]
    ring
  rw [he]
  ring

end FourPapersCommon
