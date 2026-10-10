module
public import FourPapersCommon.JointDerivativeContinuity
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! Spatial two-jet continuity for parameter families. No derivative in
the parameter is needed for multiplication or exponentiation. -/
noncomputable section
open Set
open scoped ContDiff
namespace QuantitativeFollowup
set_option maxHeartbeats 1300000
variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

structure CavityJointSpatialTwoJets (F : P×E→ℝ) : Prop where
  smooth : ∀p,ContDiff ℝ ∞ (fun y=>F (p,y))
  value : Continuous F
  first : Continuous (fun z : P×E=>fderiv ℝ (fun y=>F (z.1,y)) z.2)
  second : Continuous (fun z : P×E=>fderiv ℝ (fderiv ℝ (fun y=>F (z.1,y))) z.2)

theorem CavityJointSpatialTwoJets.exp {F : P×E→ℝ} (hF : CavityJointSpatialTwoJets F) :
    CavityJointSpatialTwoJets (fun z=>Real.exp (F z)) :=by
  have hdf(p):ContDiff ℝ ∞ (fderiv ℝ (fun y=>F (p,y))):=
    (hF.smooth p).fderiv_right (by simp)
  have he(p)(x):fderiv ℝ (fun y=>Real.exp (F (p,y))) x=
      Real.exp (F (p,x)) • fderiv ℝ (fun y=>F (p,y)) x :=
    ((hF.smooth p).differentiable (by simp) x).hasFDerivAt.exp.fderiv
  have hfirst : Continuous (fun z : P×E=>fderiv ℝ (fun y=>Real.exp (F (z.1,y))) z.2) :=by
    simp_rw [he]
    exact (Real.continuous_exp.comp hF.value).smul hF.first
  refine ⟨fun p=>(hF.smooth p).exp,(Real.continuous_exp.comp hF.value),hfirst,?_⟩
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  have hh(p)(x):fderiv ℝ (fderiv ℝ (fun y=>Real.exp (F (p,y)))) x v w=
      Real.exp (F (p,x))*fderiv ℝ (fderiv ℝ (fun y=>F (p,y))) x v w+
        (Real.exp (F (p,x))*fderiv ℝ (fun y=>F (p,y)) x v)*
          fderiv ℝ (fun y=>F (p,y)) x w :=by
    have hefun:fderiv ℝ (fun y=>Real.exp (F (p,y)))=
        fun x=>Real.exp (F (p,x)) • fderiv ℝ (fun y=>F (p,y)) x :=funext (he p)
    rw [hefun,fderiv_fun_smul ((hF.smooth p).exp.differentiable (by simp) x)
      ((hdf p).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
    rw [he]
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  simp_rw [hh]
  exact ((Real.continuous_exp.comp hF.value).mul ((hF.second.clm_apply continuous_const).clm_apply continuous_const)).add
    (((Real.continuous_exp.comp hF.value).mul (hF.first.clm_apply continuous_const)).mul
      (hF.first.clm_apply continuous_const))

theorem CavityJointSpatialTwoJets.mul {F G : P×E→ℝ}
    (hF : CavityJointSpatialTwoJets F) (hG : CavityJointSpatialTwoJets G) :
    CavityJointSpatialTwoJets (fun z=>F z*G z) :=by
  have hdF(p):ContDiff ℝ ∞ (fderiv ℝ (fun y=>F (p,y))):=(hF.smooth p).fderiv_right (by simp)
  have hdG(p):ContDiff ℝ ∞ (fderiv ℝ (fun y=>G (p,y))):=(hG.smooth p).fderiv_right (by simp)
  have he(p)(x):fderiv ℝ (fun y=>F (p,y)*G (p,y)) x=
      F (p,x) • fderiv ℝ (fun y=>G (p,y)) x+
        G (p,x) • fderiv ℝ (fun y=>F (p,y)) x :=
    fderiv_fun_mul ((hF.smooth p).differentiable (by simp) x)
      ((hG.smooth p).differentiable (by simp) x)
  have hfirst : Continuous (fun z : P×E=>fderiv ℝ (fun y=>F (z.1,y)*G (z.1,y)) z.2) :=by
    simp_rw [he]
    exact (hF.value.smul hG.first).add (hG.value.smul hF.first)
  refine ⟨fun p=>(hF.smooth p).mul (hG.smooth p),hF.value.mul hG.value,hfirst,?_⟩
  apply continuous_clm_apply.mpr
  intro v
  apply continuous_clm_apply.mpr
  intro w
  have hh(p)(x):fderiv ℝ (fderiv ℝ (fun y=>F (p,y)*G (p,y))) x v w=
      F (p,x)*fderiv ℝ (fderiv ℝ (fun y=>G (p,y))) x v w+
      fderiv ℝ (fun y=>F (p,y)) x v*fderiv ℝ (fun y=>G (p,y)) x w+
      (G (p,x)*fderiv ℝ (fderiv ℝ (fun y=>F (p,y))) x v w+
      fderiv ℝ (fun y=>G (p,y)) x v*fderiv ℝ (fun y=>F (p,y)) x w) :=by
    have hefun:fderiv ℝ (fun y=>F (p,y)*G (p,y))=
        (fun x=>F (p,x) • fderiv ℝ (fun y=>G (p,y)) x)+
          (fun x=>G (p,x) • fderiv ℝ (fun y=>F (p,y)) x) :=funext (he p)
    rw [hefun,fderiv_add (f:=fun y=>F (p,y) • fderiv ℝ (fun z=>G (p,z)) y)
      (g:=fun y=>G (p,y) • fderiv ℝ (fun z=>F (p,z)) y)
      (((hF.smooth p).smul (hdG p)).differentiable (by simp) x)
      (((hG.smooth p).smul (hdF p)).differentiable (by simp) x),
      fderiv_fun_smul ((hF.smooth p).differentiable (by simp) x) ((hdG p).differentiable (by simp) x),
      fderiv_fun_smul ((hG.smooth p).differentiable (by simp) x) ((hdF p).differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  simp_rw [hh]
  exact ((hF.value.mul ((hG.second.clm_apply continuous_const).clm_apply continuous_const)).add
    ((hF.first.clm_apply continuous_const).mul (hG.first.clm_apply continuous_const))).add
    ((hG.value.mul ((hF.second.clm_apply continuous_const).clm_apply continuous_const)).add
    ((hG.first.clm_apply continuous_const).mul (hF.first.clm_apply continuous_const)))

end QuantitativeFollowup
