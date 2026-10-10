module
public import FourPapersCommon.PartialHessianCommutation
public import FourPapersCommon.PartialGradientSmooth

@[expose] public section

/-! Parameter differentiation of the literal Riesz gradient. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem deriv_partial_gradient (U : ℝ×E→ℝ) (a : ℝ) (x : E)
    (hU : ContDiffAt ℝ ∞ U (a,x)) :
    deriv (fun α=>gradient (fun y=>U (α,y)) x) a=
      gradient (fun y=>deriv (fun α=>U (α,y)) a) x := by
  let G : ℝ→E:=fun α=>gradient (fun y=>U (α,y)) x
  have hG : ContDiffAt ℝ ∞ G a:=ContDiffAt.comp
    (f := fun α : ℝ=>(α,x))
    (g := fun z : ℝ×E=>gradient (fun y=>U (z.1,y)) z.2) a
    (contDiffAt_partial_gradient U (a,x) hU) (by fun_prop)
  have hdG:=(hG.differentiableAt (by simp)).hasDerivAt
  apply ext_inner_right ℝ
  intro w
  have hdInner:=hdG.inner ℝ (hasDerivAt_const a w)
  have he : (fun α=>inner ℝ (G α) w)=
      (fun α=>partialSpatialDerivative w U (α,x)):=by
    funext α
    exact inner_gradient_left
  have hdEq:=congrArg (fun f : ℝ→ℝ=>deriv f a) he
  rw [hdInner.deriv] at hdEq
  simp only [inner_zero_right,zero_add] at hdEq
  change inner ℝ (deriv G a) w=
    partialParamDerivative 1 (partialSpatialDerivative w U) (a,x) at hdEq
  rw [hdEq,partialParamSpatialDerivative_commute 1 w U (a,x) hU,
    inner_gradient_left]
  rfl

theorem hasDerivAt_partial_gradient (U : ℝ×E→ℝ) (a : ℝ) (x : E)
    (hU : ContDiffAt ℝ ∞ U (a,x)) :
    HasDerivAt (fun α=>gradient (fun y=>U (α,y)) x)
      (gradient (fun y=>deriv (fun α=>U (α,y)) a) x) a := by
  have hG : ContDiffAt ℝ ∞ (fun α=>gradient (fun y=>U (α,y)) x) a:=ContDiffAt.comp
    (f := fun α : ℝ=>(α,x))
    (g := fun z : ℝ×E=>gradient (fun y=>U (z.1,y)) z.2) a
    (contDiffAt_partial_gradient U (a,x) hU) (by fun_prop)
  rw [←deriv_partial_gradient U a x hU]
  exact (hG.differentiableAt (by simp)).hasDerivAt

end FourPapersCommon
