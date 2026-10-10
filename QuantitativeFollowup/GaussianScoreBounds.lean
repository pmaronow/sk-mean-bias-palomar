module
public import QuantitativeFollowup.GaussianCovarianceMatrix
public import QuantitativePaper.BoundedJets

@[expose] public section

/-! Actual Gaussian spatial scores have bounded smooth jets when the
exponent has bounded positive jets and the observable has bounded jets. -/
noncomputable section
open scoped ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem boundedJets_hessian_apply (f : QuantitativePaper.Field m→ℝ)
    (hf : BoundedPositiveJets f) (u v : QuantitativePaper.Field m) :
    BoundedJets (fun x=>vectorHessian f x u v) := by
  have hh:=(hf.boundedJets_fderiv_apply v).fderiv_apply u
  have hc : ContDiff ℝ ∞ (fderiv ℝ f) := hf.1.fderiv_right (by simp)
  have hd : Differentiable ℝ (fderiv ℝ f) := hc.differentiable (by simp)
  have he : (fun x=>fderiv ℝ (fun y=>fderiv ℝ f y v) x u)=
      (fun x=>vectorHessian f x u v) := by
    funext x
    rw [fderiv_clm_apply (hd x)
      (differentiableAt_const v)]
    simp only [fderiv_const_apply,ContinuousLinearMap.comp_zero,zero_add,
      ContinuousLinearMap.flip_apply,vectorHessian]
  rw [he] at hh
  exact hh

theorem boundedJets_gaussianScoreBilinear (V F : QuantitativePaper.Field m→ℝ)
    (hV : BoundedPositiveJets V) (hF : BoundedJets F)
    (u v : QuantitativePaper.Field m) (center : ℝ) :
    BoundedJets (fun x=>gaussianScoreBilinear V F x u v center) := by
  have hvu:=hV.boundedJets_fderiv_apply u
  have hvv:=hV.boundedJets_fderiv_apply v
  have hfu:=hF.fderiv_apply u
  have hfv:=hF.fderiv_apply v
  have hhV:=boundedJets_hessian_apply V hV u v
  have hhF:=boundedJets_hessian_apply F hF.positive u v
  have hc:=(hF.add (boundedJets_const (-center)))
  convert! ((hhF.add (hvu.mul hfv)).add (hvv.mul hfu)).add
    (hc.mul (hhV.add (hvu.mul hvv))) using 1

theorem gaussianScoreBilinear_continuous_bounded (V F : QuantitativePaper.Field m→ℝ)
    (hV : BoundedPositiveJets V) (hF : BoundedJets F)
    (u v : QuantitativePaper.Field m) (center : ℝ) :
    Continuous (fun x=>gaussianScoreBilinear V F x u v center) ∧
      ∃K : ℝ,0≤K ∧ ∀x,‖gaussianScoreBilinear V F x u v center‖≤K := by
  have hh:=boundedJets_gaussianScoreBilinear V F hV hF u v center
  refine ⟨hh.1.continuous,?_⟩
  simpa only [norm_iteratedFDeriv_zero] using hh.2 0

end QuantitativeFollowup
