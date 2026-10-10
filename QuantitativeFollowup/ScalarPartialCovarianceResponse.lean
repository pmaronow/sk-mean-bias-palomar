module
public import FourPapersCommon.ScalarFiniteStateResponseGamma

@[expose] public section

/-! Actual scalar finite-cascade covariance response at an arbitrary starting
node and spatial field. The future test is the genuine normalized finite
endpoint kernel; its later identification with the restarted diffusion is a
separate theorem. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace QuantitativeFollowup
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon
set_option maxHeartbeats 2200000
variable {k : ℕ}

def scalarSchemeFutureSquareKernel (s : RSBScheme k) (β : ℝ) (hβ : 0 < β) (h : ℝ)
    (p J : ℕ) (H : FiniteStateField (Fin 1)) : ℝ :=
  ∫ y, Paper.parisiGradient β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),y)^2
    ∂mixedSchemeEndpointKernel (AdmissibleEvenMixture.quadratic (β^2) (sq_pos_of_pos hβ))
      s (k+2-J) (J-p) (scalarSiteAbsolute h H)

theorem scalarGaussianCascade_partial_pairMoment (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (h : ℝ) (p J : ℕ) (hp : p ≤ J) (hJ : J ≤ k+2)
    (H : FiniteStateField (Fin 1)) :
    finiteStateCascadePairMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) p (J-p) (replicaSingleSiteSpinCLM H) scalarSpinAxis scalarSpinAxis=
      scalarSchemeFutureSquareKernel s β hβ h p J H := by
  let U:=finiteStateGaussianTerminalCascade (scalarSpinPotential h) (scalarSchemeMass s)
    (scalarSchemeSpinInput s β) p
  let f:=fun y=>fderiv ℝ U y scalarSpinAxis*fderiv ℝ U y scalarSpinAxis
  have hU:=contDiff_one_finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) p
  have hf : Measurable f := ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
    ((hU.continuous_fderiv (by norm_num)).clm_apply continuous_const) |>.measurable
  change sourceKernelExpectation (fun i=>scalarSpinSchemeKernel s β h (p+i)) (J-p) f
    (replicaSingleSiteSpinCLM H)=_
  rw [scalarSpinScheme_parent_mean s β h p (J-p) f hf H]
  have heF : (fun y=>f (replicaSingleSiteSpinCLM y))=
      fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-p),scalarSiteAbsolute h y)^2 := by
    funext y
    dsimp only [f,U]
    rw [fderiv_scalarGaussianTerminalCascade_axis s β hβ h p (by omega) y]
    ring
  rw [heF]
  have hg : Measurable (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-p),y)^2) := by
    exact ((Paper.continuous_parisiGradient β _).comp (continuous_const.prodMk continuous_id)).pow 2 |>.measurable
  have hb (y : ℝ) : |Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-p),y)^2| ≤ 1 := by
    have hh:=Paper.norm_parisiGradient_le_one β (Paper.parisiSchemeMeasure s) (s.q (k+2-p),y)
    rw [Real.norm_eq_abs] at hh
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp hh]
  simpa only [Nat.add_sub_of_le hp,scalarSchemeFutureSquareKernel] using
    scalarSiteScheme_parent_mean s β hβ h p (J-p) (by omega) _ hg 1 zero_le_one hb H

theorem scalarGaussianCascade_partial_diagonalMoment (s : RSBScheme k)
    (β h : ℝ) (J : ℕ) (H : FiniteStateField (Configuration 1)) (v : ℝ) (hv : 0 ≤ v) :
    finiteStateCascadeDiagonalMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) J H (finiteStateSpectralCovariance (scalarSpinDirection v))=v := by
  let _:=isMarkovKernel_finiteStateCascadeGibbsKernel (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) J
  unfold finiteStateCascadeDiagonalMoment
  simp_rw [scalarSpinDirection_spectral v hv,scalarSpinAxis_apply,mul_assoc,spin_mul_self,mul_one]
  simp

theorem scalarGaussianCascade_partial_covarianceMoment (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (h : ℝ) (p J : ℕ) (hp : p ≤ J) (hJ : J ≤ k+2)
    (H : FiniteStateField (Fin 1)) (v : ℝ) (hv : 0 ≤ v) :
    finiteStateCascadeCovarianceMoment (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) p (J-p) (replicaSingleSiteSpinCLM H)
        (finiteStateSpectralCovariance (scalarSpinDirection v))=
      v*scalarSchemeFutureSquareKernel s β hβ h p J H := by
  unfold finiteStateCascadeCovarianceMoment
  simp_rw [scalarSpinDirection_spectral v hv]
  have he (z : Configuration 1×Configuration 1) :
      v*scalarSpinAxis z.1*scalarSpinAxis z.2=v*(scalarSpinAxis z.1*scalarSpinAxis z.2) := by ring
  simp_rw [he]
  rw [integral_const_mul,←finiteStateCascadePairMoment_eq_splitLaw (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) p (J-p)
    (replicaSingleSiteSpinCLM H),scalarGaussianCascade_partial_pairMoment s β hβ h p J hp hJ H]

theorem scalarGaussianCascade_partial_response (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (h : ℝ) (j J : ℕ) (hj : j < J) (hJ : J ≤ k+2)
    (H : FiniteStateField (Fin 1)) (v : ℝ) (hv : 0 ≤ v) :
    finiteStateCascadeCovarianceResponse (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) j (J-j) (replicaSingleSiteSpinCLM H) (scalarSpinDirection v)=
      v*(1+∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
        scalarSchemeFutureSquareKernel s β hβ h (p+1) J H) := by
  rw [finiteStateCascadeCovarianceResponse_eq_split_moments (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s)]
  rw [show j+(J-j)=J by omega,scalarGaussianCascade_partial_diagonalMoment s β h J _ v hv]
  have hm : scalarSchemeMass s 0=1 := by simp [scalarSchemeMass,s.m_top]
  rw [hm,sub_self,zero_mul,add_zero]
  have he : (∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
      finiteStateCascadeCovarianceMoment (scalarSpinPotential h) (scalarSchemeMass s)
        (scalarSchemeSpinInput s β) (p+1) (J-(p+1)) (replicaSingleSiteSpinCLM H)
        (finiteStateSpectralCovariance (scalarSpinDirection v)))=
      v*∑p∈Finset.range j,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
        scalarSchemeFutureSquareKernel s β hβ h (p+1) J H := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [scalarGaussianCascade_partial_covarianceMoment s β hβ h (p+1) J (by
      have hpj:=Finset.mem_range.mp hp
      omega) hJ H v hv]
    ring
  rw [he]
  ring

end QuantitativeFollowup
