module
public import QuantitativeFollowup.ScalarPartialCovarianceResponse

@[expose] public section

/-! The genuine scalar Hessian/gradient boundary expression is exactly the
local normalized cascade covariance response, with every finite node and
starting field allowed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Real
open scoped BigOperators
namespace QuantitativeFollowup
open OverlapPaper SpinGlass SpinGlass.Targets SpinGlass.AT FourPapersCommon
set_option maxHeartbeats 2600000
variable {k : ℕ}

theorem fderiv_scalarGaussianTerminalCascade_second_axis (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (h : ℝ) (j : ℕ) (hj : j ≤ k+2)
    (H : FiniteStateField (Fin 1)) :
    fderiv ℝ (fderiv ℝ (finiteStateGaussianTerminalCascade (scalarSpinPotential h)
      (scalarSchemeMass s) (scalarSchemeSpinInput s β) j)) (replicaSingleSiteSpinCLM H)
        scalarSpinAxis scalarSpinAxis=
      Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),scalarSiteAbsolute h H) := by
  let U:=finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeSpinInput s β) j
  let e:FiniteStateField (Fin 1):=EuclideanSpace.single 0 1
  let g:=fun y=>fderiv ℝ U y scalarSpinAxis
  have hU:=contDiff_two_finiteStateGaussianTerminalCascade (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) j
  have hD : ContDiff ℝ 1 (fderiv ℝ U) := hU.fderiv_right (by norm_num)
  have hi:=((hasDerivAt_id (0 : ℝ)).smul_const e).const_add H
  have hiT:=(replicaSingleSiteSpinCLM (d:=1)).hasFDerivAt.comp_hasDerivAt 0 hi
  have hiT' : HasDerivAt (fun x : ℝ=>replicaSingleSiteSpinCLM (H+x • e)) scalarSpinAxis 0 := by
    simpa only [Function.comp_def,id_eq,one_smul,zero_smul,add_zero,scalarSpinAxis,e] using hiT
  have hd:=((hD.differentiable (by norm_num) (replicaSingleSiteSpinCLM (H+(0:ℝ) • e))).hasFDerivAt.clm_apply
    (hasFDerivAt_const scalarSpinAxis (replicaSingleSiteSpinCLM (H+(0:ℝ) • e)))).comp_hasDerivAt 0 hiT'
  have he : (fun x : ℝ=>g (replicaSingleSiteSpinCLM (H+x • e)))=
      fun x=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-j),scalarSiteAbsolute h H+x) := by
    funext x
    dsimp only [g,U]
    rw [fderiv_scalarGaussianTerminalCascade_axis s β hβ h j hj (H+x • e)]
    simp only [scalarSiteAbsolute,WithLp.ofLp_add,Pi.add_apply,WithLp.ofLp_smul,
      Pi.smul_apply,smul_eq_mul,e,EuclideanSpace.single_apply,ite_true,mul_one]
    congr 2
    ring
  have hd' : HasDerivAt (fun x : ℝ=>g (replicaSingleSiteSpinCLM (H+x • e)))
      (fderiv ℝ (fderiv ℝ U) (replicaSingleSiteSpinCLM H) scalarSpinAxis scalarSpinAxis) 0 := by
    simpa [Function.comp_def,g,scalarSpinAxis,e] using hd
  rw [he] at hd'
  have hP0 : HasDerivAt (fun y=>Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
      (s.q (k+2-j),y))
      (Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (s.q (k+2-j),scalarSiteAbsolute h H))
      (scalarSiteAbsolute h H+0) := by
    simpa only [add_zero] using Paper.hasDerivAt_parisiGradient_spatial_all β
      (Paper.parisiSchemeMeasure s) (s.q (k+2-j)) (scalarSiteAbsolute h H)
  have hP:=hP0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_add (scalarSiteAbsolute h H))
  exact hd'.unique (by simpa only [Function.comp_def,id_eq,zero_add,add_zero,mul_one] using hP)

theorem scalarGaussianCascade_local_response (s : RSBScheme k)
    (β : ℝ) (hβ : 0 < β) (h : ℝ) (J : ℕ) (hJ : J ≤ k+2)
    (H : FiniteStateField (Fin 1)) :
    Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (s.q (k+2-J),scalarSiteAbsolute h H)+
      scalarSchemeMass s J*Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
        (s.q (k+2-J),scalarSiteAbsolute h H)^2=
      1+∑p∈Finset.range J,(scalarSchemeMass s (p+1)-scalarSchemeMass s p)*
        scalarSchemeFutureSquareKernel s β hβ h (p+1) J H := by
  have hr:=finiteStateCascadeCovarianceResponse_eq_split_moments (scalarSpinPotential h)
    (scalarSchemeMass s) (scalarSchemeMass_nonneg s) (scalarSchemeSpinInput s β) J 0
      (replicaSingleSiteSpinCLM H) (scalarSpinDirection 1)
  rw [Nat.add_zero,scalarGaussianCascade_partial_diagonalMoment s β h J _ 1 zero_le_one] at hr
  have hm : scalarSchemeMass s 0=1 := by simp [scalarSchemeMass,s.m_top]
  rw [hm,sub_self,zero_mul,add_zero] at hr
  have he (p : ℕ) (hp : p∈Finset.range J) :
      finiteStateCascadeCovarianceMoment (scalarSpinPotential h) (scalarSchemeMass s)
        (scalarSchemeSpinInput s β) (p+1) (J-(p+1)) (replicaSingleSiteSpinCLM H)
          (finiteStateSpectralCovariance (scalarSpinDirection 1))=
        scalarSchemeFutureSquareKernel s β hβ h (p+1) J H := by
    simpa only [one_mul] using scalarGaussianCascade_partial_covarianceMoment s β hβ h (p+1) J
      (by have hh:=Finset.mem_range.mp hp; omega) hJ H 1 zero_le_one
  have hs := Finset.sum_congr (s₁:=Finset.range J) (s₂:=Finset.range J) rfl
    (fun p hp=>congrArg ((scalarSchemeMass s (p+1)-scalarSchemeMass s p)*·) (he p hp))
  rw [hs] at hr
  have hl : finiteStateCascadeCovarianceResponse (scalarSpinPotential h) (scalarSchemeMass s)
      (scalarSchemeSpinInput s β) J 0 (replicaSingleSiteSpinCLM H) (scalarSpinDirection 1)=
      Paper.parisiHessian β (Paper.parisiSchemeMeasure s) (s.q (k+2-J),scalarSiteAbsolute h H)+
        scalarSchemeMass s J*Paper.parisiGradient β (Paper.parisiSchemeMeasure s)
          (s.q (k+2-J),scalarSiteAbsolute h H)^2 := by
    unfold finiteStateCascadeCovarianceResponse
    simp only [Fin.sum_univ_one,sourceKernelExpectation,scalarSpinDirection_single,
      Real.sqrt_one,one_smul]
    rw [fderiv_scalarGaussianTerminalCascade_second_axis s β hβ h J hJ H,
      fderiv_scalarGaussianTerminalCascade_axis s β hβ h J hJ H]
    ring
  exact hl.symm.trans hr

end QuantitativeFollowup
