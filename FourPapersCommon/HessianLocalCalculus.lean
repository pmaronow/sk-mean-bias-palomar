module
public import FourPapersCommon.LocalGradientCalculus
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

/-! Local calculus of literal Hessian operators, including the norm-square
term in the energy-scaled Legendre equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
open QuantitativeFollowup
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hessianOperator_congr_of_eventuallyEq (f g : E→ℝ) (x : E)
    (he : f=ᶠ[𝓝 x]g) : hessianOperator f x=hessianOperator g x := by
  unfold hessianOperator
  rw [he.fderiv.fderiv_eq]

theorem hessianOperator_add_at (f g : E→ℝ) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    hessianOperator (fun y=>f y+g y) x=hessianOperator f x+hessianOperator g x := by
  have he : fderiv ℝ (fun y=>f y+g y)=ᶠ[𝓝 x](fderiv ℝ f+fderiv ℝ g) := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with y hfy hgy
    exact fderiv_fun_add (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  have hdF := (hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  have hdG := (hg.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.add_apply,inner_add_left,inner_hessianOperator,
    inner_hessianOperator,inner_hessianOperator,he.fderiv_eq,fderiv_add hdF hdG]
  rfl

theorem hessianOperator_const_mul_at (f : E→ℝ) (x : E) (c : ℝ)
    (hf : ContDiffAt ℝ 2 f x) :
    hessianOperator (fun y=>c*f y) x=c • hessianOperator f x := by
  have he : fderiv ℝ (fun y=>c*f y)=ᶠ[𝓝 x](c • fderiv ℝ f) := by
    filter_upwards [hf.eventually (by norm_num)] with y hfy
    exact fderiv_fun_const_smul (hfy.differentiableAt (by norm_num)) c
  have hdF := (hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt (by norm_num)
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [ContinuousLinearMap.smul_apply,real_inner_smul_left,inner_hessianOperator,
    inner_hessianOperator,he.fderiv_eq,fderiv_const_smul hdF c]
  rfl

theorem hessianOperator_norm_sq (x : E) :
    hessianOperator (fun y : E=>‖y‖^2) x=(2 : ℝ) • (1 : E→L[ℝ]E) := by
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  rw [inner_hessianOperator,fderiv_norm_sq,
    fderiv_const_smul (innerSL ℝ).differentiableAt 2,(innerSL ℝ).fderiv]
  simp [real_inner_smul_left]
  rfl

end FourPapersCommon
