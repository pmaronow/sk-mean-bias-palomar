module
public import FourPapersCommon.PartialGradientCommutation
public import FourPapersCommon.LocalGradientCalculus
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! Actual second differentiation of a stationary Legendre value, with
the inverse-field derivative obtained from its true gradient equation. -/
noncomputable section
open Filter
open scoped Topology ContDiff
namespace FourPapersCommon
open QuantitativeFollowup
set_option maxHeartbeats 2200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hasDerivAt_stationary_inverse_curve (U : ℝ×E→ℝ) (Y : ℝ→E) (a : ℝ) (m : E)
    (hU : ContDiffAt ℝ ∞ U (a,Y a)) (hY : DifferentiableAt ℝ Y a)
    (hStationary : (fun α=>gradient (fun x=>U (α,x)) (Y α))=ᶠ[𝓝 a](fun _=>m))
    (hUnit : IsUnit (hessianOperator (fun x=>U (a,x)) (Y a))) :
    HasDerivAt Y
      (-((Ring.inverse (hessianOperator (fun x=>U (a,x)) (Y a)))
        (gradient (fun x=>deriv (fun α=>U (α,x)) a) (Y a)))) a := by
  let G : ℝ×E→E:=fun z=>gradient (fun x=>U (z.1,x)) z.2
  let H:=hessianOperator (fun x=>U (a,x)) (Y a)
  let w:=gradient (fun x=>deriv (fun α=>U (α,x)) a) (Y a)
  let v:=deriv Y a
  have hG : ContDiffAt ℝ ∞ G (a,Y a):=contDiffAt_partial_gradient U (a,Y a) hU
  have hdG:=(hG.differentiableAt (by simp)).hasFDerivAt
  have hdParam:=hasDerivAt_partial_gradient U a (Y a) hU
  have hdP:=hdG.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a (Y a)))
  have hP : (fderiv ℝ G (a,Y a)) (1,0)=w:=hdP.unique hdParam
  have hf : ContDiffAt ℝ 2 (fun x=>U (a,x)) (Y a):=
    (hU.comp (Y a) (contDiffAt_const.prodMk contDiffAt_id)).of_le (by norm_num)
  have hdSpatial:=hasFDerivAt_gradient_of_contDiffAt _ (Y a) hf
  have hdX:=hdG.comp (Y a) ((hasFDerivAt_const a (Y a)).prodMk (hasFDerivAt_id (Y a)))
  have hX (z : E) : (fderiv ℝ G (a,Y a)) (0,z)=H z:=by
    have he:=congrArg (fun L : E→L[ℝ]E=>L z) (hdX.unique hdSpatial)
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply] using he
  have hdTotal:=hdG.comp_hasDerivAt a ((hasDerivAt_id a).prodMk hY.hasDerivAt)
  have hZero : (fderiv ℝ G (a,Y a)) (1,v)=0:=
    (hdTotal.congr_of_eventuallyEq hStationary.symm).unique (hasDerivAt_const a m)
  have heSplit : (fderiv ℝ G (a,Y a)) (1,v)=w+H v:=by
    rw [show ((1,v) : ℝ×E)=(1,0)+(0,v) by simp,map_add,hP,hX]
  have hHv : H v= -w:=by
    rw [heSplit,add_comm] at hZero
    exact eq_neg_of_add_eq_zero_left hZero
  obtain ⟨u,hu⟩:=hUnit
  have hInverse : (Ring.inverse H)*H=(1 : E→L[ℝ]E):=by
    change (Ring.inverse (hessianOperator (fun x=>U (a,x)) (Y a)))*
      hessianOperator (fun x=>U (a,x)) (Y a)=_
    rw [←hu,Ring.inverse_unit]
    exact u.inv_val
  have hv : v= -(Ring.inverse H) w:=by
    have he:=congrArg (Ring.inverse H : E→L[ℝ]E) hHv
    rw [map_neg] at he
    have hLeft : (Ring.inverse H) (H v)=v:=by
      change ((Ring.inverse H)*H) v=v
      rw [hInverse]
      rfl
    rwa [hLeft] at he
  apply hY.hasDerivAt.congr_deriv
  exact hv

theorem stationary_second_variation (U : ℝ×E→ℝ) (Y : ℝ→E) (Φ : ℝ→ℝ)
    (a c : ℝ) (m : E) (hU : ContDiffAt ℝ ∞ U (a,Y a))
    (hY : DifferentiableAt ℝ Y a)
    (hStationary : (fun α=>gradient (fun x=>U (α,x)) (Y α))=ᶠ[𝓝 a](fun _=>m))
    (hUnit : IsUnit (hessianOperator (fun x=>U (a,x)) (Y a)))
    (hFirst : ∀ᶠ α in 𝓝 a,HasDerivAt Φ
      (-c*deriv (fun θ=>U (θ,Y α)) α) α) :
    deriv (deriv Φ) a=c*(-deriv (deriv (fun α=>U (α,Y a))) a+
      inner ℝ (gradient (fun x=>deriv (fun α=>U (α,x)) a) (Y a))
        ((Ring.inverse (hessianOperator (fun x=>U (a,x)) (Y a)))
          (gradient (fun x=>deriv (fun α=>U (α,x)) a) (Y a)))) := by
  let W : ℝ×E→ℝ:=partialParamDerivative (1 : ℝ) U
  have hW : ContDiffAt ℝ ∞ W (a,Y a):=contDiffAt_partialParamDerivative 1 U (a,Y a) hU
  have hdW:=(hW.differentiableAt (by simp)).hasFDerivAt
  have hdY:=hasDerivAt_stationary_inverse_curve U Y a m hU hY hStationary hUnit
  have hdComp:=hdW.comp_hasDerivAt a ((hasDerivAt_id a).prodMk hdY)
  simp only [Function.comp_def,id_eq] at hdComp
  have hPartial : (fderiv ℝ W (a,Y a)) (1,0)=deriv (deriv (fun α=>U (α,Y a))) a:=by
    have hd:=(hdW.comp_hasDerivAt a ((hasDerivAt_id a).prodMk (hasDerivAt_const a (Y a)))).deriv
    simpa only [Function.comp_def,id_eq,W,partialParamDerivative,fderiv_apply_one_eq_deriv] using hd.symm
  have hSpace (z : E) : (fderiv ℝ W (a,Y a)) (0,z)=
      inner ℝ (gradient (fun x=>deriv (fun α=>U (α,x)) a) (Y a)) z:=by
    have hd:=hdW.comp (Y a) ((hasFDerivAt_const a (Y a)).prodMk (hasFDerivAt_id (Y a)))
    have he:=congrArg (fun L : E→L[ℝ]ℝ=>L z) hd.fderiv
    rw [←inner_gradient_left] at he
    simpa only [Function.comp_def,id_eq,W,partialParamDerivative,fderiv_apply_one_eq_deriv,
      ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.zero_apply,ContinuousLinearMap.id_apply] using he.symm
  have he : deriv Φ=ᶠ[𝓝 a](fun α=>-c*W (α,Y α)):=by
    filter_upwards [hFirst] with α hα
    simpa only [W,partialParamDerivative,fderiv_apply_one_eq_deriv] using hα.deriv
  rw [he.deriv_eq,(hdComp.const_mul (-c)).deriv]
  have hs : ∀z : E,(fderiv ℝ W (a,Y a)) (1,z)=
      (fderiv ℝ W (a,Y a)) (1,0)+(fderiv ℝ W (a,Y a)) (0,z):=by
    intro z
    rw [←map_add]
    simp
  rw [hs,hPartial,hSpace,inner_neg_right]
  ring

end FourPapersCommon
