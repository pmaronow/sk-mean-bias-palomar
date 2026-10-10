module
public import QuantitativeFollowup.GaussianLinearCurveResponse

@[expose] public section

/-! Literal score and Hessian algebra of an exponentially weighted
observable, used in normalized Gaussian covariance differentiation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem fderiv_exp_mul_observable (V F : Field n → ℝ)
    (hV : Differentiable ℝ V) (hF : Differentiable ℝ F) (x b : Field n) :
    fderiv ℝ (fun y => Real.exp (V y)*F y) x b=
      Real.exp (V x)*(fderiv ℝ V x b*F x+fderiv ℝ F x b) := by
  have he := ((hV x).hasFDerivAt.exp.mul (hF x).hasFDerivAt).fderiv
  have hh := congrArg (fun D : Field n →L[ℝ] ℝ => D b) he
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,Pi.mul_apply] at hh
  calc
    _ = Real.exp (V x)*fderiv ℝ F x b+F x*(Real.exp (V x)*fderiv ℝ V x b) := by convert! hh using 1
    _ = _ := by ring

 theorem hasFDerivAt_directional_field (F : Field n → ℝ) (hF : ContDiff ℝ 2 F)
    (x b : Field n) :
    HasFDerivAt (fun y => fderiv ℝ F y b) ((vectorHessian F x).flip b) x := by
  have hdF := (hF.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  simpa only [ContinuousLinearMap.comp_zero,zero_add,vectorHessian] using
    (hdF x).hasFDerivAt.clm_apply (hasFDerivAt_const b x)

 theorem vectorHessian_exp_mul_observable (V F : Field n → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (x a b : Field n) :
    vectorHessian (fun y => Real.exp (V y)*F y) x a b=
      Real.exp (V x)*(vectorHessian F x a b+
        fderiv ℝ V x a*fderiv ℝ F x b+fderiv ℝ V x b*fderiv ℝ F x a+
        F x*(vectorHessian V x a b+fderiv ℝ V x a*fderiv ℝ V x b)) := by
  have hdV := hV.differentiable (by norm_num)
  have hdF := hF.differentiable (by norm_num)
  have hW : ContDiff ℝ 2 (fun y => Real.exp (V y)*F y) := hV.exp.mul hF
  have he : (fun y => fderiv ℝ (fun z => Real.exp (V z)*F z) y b)=
      (fun y => Real.exp (V y)*(fderiv ℝ V y b*F y+fderiv ℝ F y b)) :=
    funext fun y => fderiv_exp_mul_observable V F hdV hdF y b
  have hleft := hasFDerivAt_directional_field (fun y => Real.exp (V y)*F y) hW x b
  rw [he] at hleft
  have hright := ((hdV x).hasFDerivAt.exp).mul
    (((hasFDerivAt_directional_field V hV x b).mul (hdF x).hasFDerivAt).add
      (hasFDerivAt_directional_field F hF x b))
  have hD := hleft.unique hright
  have ha := congrArg (fun D : Field n →L[ℝ] ℝ => D a) hD
  simp only [ContinuousLinearMap.flip_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Pi.mul_apply,Pi.add_apply] at ha
  rw [ha]
  ring

 theorem vectorHessian_exp_potential (V : Field n → ℝ)
    (hV : ContDiff ℝ 2 V) (x a b : Field n) :
    vectorHessian (fun y => Real.exp (V y)) x a b=
      Real.exp (V x)*(vectorHessian V x a b+fderiv ℝ V x a*fderiv ℝ V x b) := by
  have he := vectorHessian_exp_mul_observable V (fun _ => 1) hV contDiff_const x a b
  simpa [vectorHessian] using he

end QuantitativeFollowup
