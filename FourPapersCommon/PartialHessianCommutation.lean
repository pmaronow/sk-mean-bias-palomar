module
public import FourPapersCommon.PartialDerivativeCommutation
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Genuine parameter differentiation commutes with the actual spatial
Hessian. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
open QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inner_partial_hessian (U : ℝ×E→ℝ) (a : ℝ) (x v w : E)
    (hU : ContDiffAt ℝ 2 U (a,x)) :
    inner ℝ (hessianOperator (fun y=>U (a,y)) x v) w=
      partialSpatialDerivative v (partialSpatialDerivative w U) (a,x) := by
  let f : E→ℝ:=fun y=>U (a,y)
  have hf : ContDiffAt ℝ 2 f x:=hU.comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hd:=((hf.fderiv_right (by norm_num : (1 : ℕ∞ω)+1≤2)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have he:=congrArg (fun L : E→L[ℝ]ℝ=>L v) hd.fderiv
  rw [inner_hessianOperator]
  change fderiv ℝ (fderiv ℝ f) x v w=fderiv ℝ (fun y=>fderiv ℝ f y w) x v
  simpa only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,add_zero,ContinuousLinearMap.flip_apply] using he.symm

theorem deriv_partial_hessian (U : ℝ×E→ℝ) (a : ℝ) (x : E)
    (hU : ContDiffAt ℝ ∞ U (a,x)) :
    deriv (fun α=>hessianOperator (fun y=>U (α,y)) x) a=
      hessianOperator (fun y=>deriv (fun α=>U (α,y)) a) x := by
  let H : ℝ→E→L[ℝ]E:=fun α=>hessianOperator (fun y=>U (α,y)) x
  have hH : ContDiffAt ℝ ∞ H a:=ContDiffAt.comp
    (f := fun α : ℝ=>(α,x))
    (g := fun z : ℝ×E=>hessianOperator (fun y=>U (z.1,y)) z.2) a
    (contDiffAt_partial_hessian U (a,x) hU) (by fun_prop)
  have hdH:=((hH.differentiableAt (by simp)).hasDerivAt)
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_right ℝ
  intro w
  have hdInner:=(hdH.clm_apply (hasDerivAt_const a v)).inner ℝ (hasDerivAt_const a w)
  have hInner : (fun α=>inner ℝ (H α v) w)=ᶠ[𝓝 a]
      (fun α=>partialSpatialDerivative v (partialSpatialDerivative w U) (α,x)):=by
    have hn := ((continuous_id.prodMk continuous_const).tendsto a).eventually
      ((hU.of_le (by norm_num : (3 : ℕ∞ω)≤∞)).eventually (by norm_num))
    filter_upwards [hn] with α hα
    exact inner_partial_hessian U α x v w (hα.of_le (by norm_num))
  have he : inner ℝ ((deriv H a) v) w=
      partialParamDerivative 1 (partialSpatialDerivative v (partialSpatialDerivative w U)) (a,x):=by
    have he' := hInner.deriv_eq
    rw [hdInner.deriv] at he'
    simpa only [inner_zero_right,add_zero,map_zero,zero_add,partialParamDerivative,
      fderiv_apply_one_eq_deriv] using he'
  rw [he,partialParamSpatialDerivative_commute_third 1 v w U (a,x) hU]
  have hP:=contDiffAt_partialParamDerivative (1 : ℝ) U (a,x) hU
  have hRight:=inner_partial_hessian (partialParamDerivative (1 : ℝ) U) a x v w
    (hP.of_le (by norm_num))
  exact hRight.symm

theorem hasDerivAt_partial_hessian (U : ℝ×E→ℝ) (a : ℝ) (x : E)
    (hU : ContDiffAt ℝ ∞ U (a,x)) :
    HasDerivAt (fun α=>hessianOperator (fun y=>U (α,y)) x)
      (hessianOperator (fun y=>deriv (fun α=>U (α,y)) a) x) a := by
  have hH : ContDiffAt ℝ ∞ (fun α=>hessianOperator (fun y=>U (α,y)) x) a:=
    ContDiffAt.comp (f := fun α : ℝ=>(α,x))
      (g := fun z : ℝ×E=>hessianOperator (fun y=>U (z.1,y)) z.2) a
      (contDiffAt_partial_hessian U (a,x) hU) (by fun_prop)
  rw [←deriv_partial_hessian U a x hU]
  exact (hH.differentiableAt (by simp)).hasDerivAt

end FourPapersCommon
