module
public import QuantitativeFollowup.GaussianParameterResponse

@[expose] public section

/-! The literal normalized Gaussian response with simultaneous changes in
an observable, its exponential density, and its covariance. This is the
three-term formula used before the scalar finite-profile cancellations. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}
variable {a : ℝ} {x : Field m}

theorem continuous_gaussianParameterDerivative (F : ℝ → Field m → ℝ)
    (hF : ContDiff ℝ 2 (Function.uncurry F)) :
    Continuous (fun p : ℝ×Field m => gaussianParameterDerivative F p.1 p.2) := by
  exact ((hF.fderiv_right (m := 1) (by norm_num)).continuous).clm_apply continuous_const

theorem continuous_gaussianParameterDerivative_slice (F : ℝ → Field m → ℝ) (a : ℝ)
    (hF : ∀y,ContDiffAt ℝ 2 (Function.uncurry F) (a,y)) :
    Continuous (gaussianParameterDerivative F a) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  exact (((hF y).continuousAt_fderiv (by norm_num)).comp
    (continuous_const.prodMk continuous_id).continuousAt).clm_apply continuousAt_const

theorem gaussianParameterDerivative_exp_mul (V F : ℝ → Field m → ℝ)
    (hV : DifferentiableAt ℝ (Function.uncurry V) (a,x))
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a,x)) :
    gaussianParameterDerivative (fun u y => Real.exp (V u y)*F u y) a x=
      Real.exp (V a x)*(gaussianParameterDerivative F a x+F a x*gaussianParameterDerivative V a x) := by
  have hh := congrArg (fun D : (ℝ×Field m) →L[ℝ] ℝ => D (1,0))
    (hV.hasFDerivAt.exp.mul hF.hasFDerivAt).fderiv
  simp only [add_apply,smul_apply,smul_eq_mul] at hh
  change _=_
  calc
    _=Real.exp (V a x)*gaussianParameterDerivative F a x+
      F a x*(Real.exp (V a x)*gaussianParameterDerivative V a x) := by convert! hh using 1
    _=_ := by ring

theorem gaussianParameterDerivative_exp (V : ℝ → Field m → ℝ)
    (hV : DifferentiableAt ℝ (Function.uncurry V) (a,x)) :
    gaussianParameterDerivative (fun u y => Real.exp (V u y)) a x=
      Real.exp (V a x)*gaussianParameterDerivative V a x := by
  have hh := congrArg (fun D : (ℝ×Field m) →L[ℝ] ℝ => D (1,0)) hV.hasFDerivAt.exp.fderiv
  simp only [smul_apply,smul_eq_mul] at hh
  convert! hh using 1

def gaussianExplicitCenteredScore (V F : ℝ → Field m → ℝ) (a : ℝ) (x : Field m) (c : ℝ) : ℝ :=
  gaussianParameterDerivative F a x+(F a x-c)*gaussianParameterDerivative V a x

theorem gaussianExplicitCenteredScore_exp_identity (V F : ℝ → Field m → ℝ)
    (hV : DifferentiableAt ℝ (Function.uncurry V) (a,x))
    (hF : DifferentiableAt ℝ (Function.uncurry F) (a,x)) (c : ℝ) :
    Real.exp (V a x)*gaussianExplicitCenteredScore V F a x c=
      gaussianParameterDerivative (fun u y => Real.exp (V u y)*F u y) a x-
        c*gaussianParameterDerivative (fun u y => Real.exp (V u y)) a x := by
  rw [gaussianParameterDerivative_exp_mul V F hV hF,gaussianParameterDerivative_exp V hV]
  unfold gaussianExplicitCenteredScore
  ring

theorem hasDerivAt_gaussian_weighted_parameter_response (V F : ℝ → Field m → ℝ)
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hV : ∀u∈S,∀y,ContDiffAt ℝ 2 (Function.uncurry V) (u,y))
    (hF : ∀u∈S,∀y,ContDiffAt ℝ 2 (Function.uncurry F) (u,y))
    (dF : ∀u,VectorHeatDatum (fun y => Real.exp (V u y)*F u y))
    (dH : ∀u,VectorHeatDatum (fun y => Real.exp (V u y)))
    (hAB : ∀u∈S,HasDerivAt A (B u) u) (C R K L : ℝ≥0)
    (hA : ∀u∈S,‖A u‖ ≤ K) (hB : ∀u∈S,‖B u‖ ≤ L)
    (hfirstF : ∀u∈S,∀y,‖fderiv ℝ (fun z => Real.exp (V u z)*F u z) y‖ ≤ C*Real.exp (R*‖y‖))
    (hfirstH : ∀u∈S,∀y,‖fderiv ℝ (fun z => Real.exp (V u z)) y‖ ≤ C*Real.exp (R*‖y‖))
    (hpartialF : ∀u∈S,∀y,‖gaussianParameterDerivative (fun v z => Real.exp (V v z)*F v z) u y‖ ≤ C*Real.exp (R*‖y‖))
    (hpartialH : ∀u∈S,∀y,‖gaussianParameterDerivative (fun v z => Real.exp (V v z)) u y‖ ≤ C*Real.exp (R*‖y‖))
    (x : Field m) (hH : gaussianLinearMean (fun y => Real.exp (V a y)) (A a) x≠0) :
    HasDerivAt (fun u => gaussianLinearNormalizedMean (fun y => Real.exp (V u y)*F u y)
      (fun y => Real.exp (V u y)) (A u) x)
      ((∫z,Real.exp (V a (x+A a z))*(
        gaussianExplicitCenteredScore V F a (x+A a z)
          (gaussianLinearNormalizedMean (fun y => Real.exp (V a y)*F a y) (fun y => Real.exp (V a y)) (A a) x)+
        ∑i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1))
          (gaussianLinearNormalizedMean (fun y => Real.exp (V a y)*F a y) (fun y => Real.exp (V a y)) (A a) x))
        ∂fieldGaussian n)/gaussianLinearMean (fun y => Real.exp (V a y)) (A a) x) a := by
  let WF := fun u (y : Field m) => Real.exp (V u y)*F u y
  let WH := fun u (y : Field m) => Real.exp (V u y)
  let c := gaussianLinearNormalizedMean (WF a) (WH a) (A a) x
  have ha : a∈S := mem_of_mem_nhds hS
  have hWF (u) (hu : u∈S) (y) : ContDiffAt ℝ 2 (Function.uncurry WF) (u,y) :=
    (hV u hu y).exp.mul (hF u hu y)
  have hWH (u) (hu : u∈S) (y) : ContDiffAt ℝ 2 (Function.uncurry WH) (u,y) :=
    (hV u hu y).exp
  have hpaF : AEStronglyMeasurable (fun z => gaussianParameterDerivative WF a (x+A a z)) (fieldGaussian n) :=
    ((continuous_gaussianParameterDerivative_slice WF a (hWF a ha)).comp
      (continuous_const.add (A a).continuous)).aestronglyMeasurable
  have hpaH : AEStronglyMeasurable (fun z => gaussianParameterDerivative WH a (x+A a z)) (fieldGaussian n) :=
    ((continuous_gaussianParameterDerivative_slice WH a (hWH a ha)).comp
      (continuous_const.add (A a).continuous)).aestronglyMeasurable
  have hdF := hasDerivAt_gaussianLinearParameterMean WF A B a S hS dF
    (fun u hu y => (hWF u hu y).differentiableAt (by norm_num)) hAB C R K L hA hB hfirstF hpartialF x hpaF
  have hdH := hasDerivAt_gaussianLinearParameterMean WH A B a S hS dH
    (fun u hu y => (hWH u hu y).differentiableAt (by norm_num)) hAB C R K L hA hB hfirstH hpartialH x hpaH
  have hipF : Integrable (fun z => gaussianParameterDerivative WF a (x+A a z)) (fieldGaussian n) := by
    apply ((SYK.integrable_exp_mul_norm (ι := Fin n) (R*K)).const_mul
      (C*Real.exp (R*‖x‖))).mono' hpaF
    exact .of_forall (gaussianParameterDerivative_input_bound WF (A a) a x C R K (hpartialF a ha) (hA a ha))
  have hipH : Integrable (fun z => gaussianParameterDerivative WH a (x+A a z)) (fieldGaussian n) := by
    apply ((SYK.integrable_exp_mul_norm (ι := Fin n) (R*K)).const_mul
      (C*Real.exp (R*‖x‖))).mono' hpaH
    exact .of_forall (gaussianParameterDerivative_input_bound WH (A a) a x C R K (hpartialH a ha) (hA a ha))
  have he (z : Field n) : Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c=
      gaussianParameterDerivative WF a (x+A a z)-c*gaussianParameterDerivative WH a (x+A a z) :=
    gaussianExplicitCenteredScore_exp_identity V F ((hV a ha _).differentiableAt (by norm_num))
      ((hF a ha _).differentiableAt (by norm_num)) c
  have hip : Integrable (fun z => Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c) (fieldGaussian n) := by
    simp_rw [he]
    exact hipF.sub (hipH.const_mul c)
  have his := integral_gaussian_centered_score (V a) (F a)
    (contDiff_iff_contDiffAt.mpr (fun y => (hV a ha y).comp y
      (contDiffAt_const.prodMk contDiffAt_id)))
    (contDiff_iff_contDiffAt.mpr (fun y => (hF a ha y).comp y
      (contDiffAt_const.prodMk contDiffAt_id)))
    (dF a) (dH a) (A a) (B a) x c
  apply (hdF.div hdH hH).congr_deriv
  rw [show (fun z => Real.exp (V a (x+A a z))*(gaussianExplicitCenteredScore V F a (x+A a z) c+
      ∑ i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
        (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) c))=
      (fun z => Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c)+
        (fun z => Real.exp (V a (x+A a z))*∑ i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) c) from by
      funext z;exact mul_add _ _ _]
  have hadd : integral (fieldGaussian n)
      ((fun z => Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c)+
        (fun z => Real.exp (V a (x+A a z))*∑ i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) c))=
      (∫z,Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c ∂fieldGaussian n)+
        (∫z,Real.exp (V a (x+A a z))*∑ i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) c ∂fieldGaussian n) := by
    convert! integral_add hip his.1 using 1
  rw [hadd,his.2]
  simp_rw [he]
  rw [integral_sub hipF (hipH.const_mul c),integral_const_mul]
  dsimp only [c,gaussianLinearNormalizedMean,WF,WH]
  field_simp [hH]
  ring

end QuantitativeFollowup
