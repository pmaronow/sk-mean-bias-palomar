module
public import QuantitativeFollowup.GaussianWeakParameterResponse

@[expose] public section

/-! The actual unnormalized centered Gaussian parameter response. Keeping
the centering constant arbitrary allows finite marks to be summed before
normalization, as required by the joint Gaussian/spin density. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem hasDerivAt_gaussian_centered_parameter_mean (V F : ℝ → Field m → ℝ)
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hV : ∀u∈S,∀y,DifferentiableAt ℝ (Function.uncurry V) (u,y))
    (hF : ∀u∈S,∀y,DifferentiableAt ℝ (Function.uncurry F) (u,y))
    (hVa : ContDiff ℝ 2 (V a)) (hFa : ContDiff ℝ 2 (F a))
    (hmV : Measurable (gaussianParameterDerivative V a))
    (hmF : Measurable (gaussianParameterDerivative F a))
    (dF : ∀u,VectorHeatDatum (fun y => Real.exp (V u y)*F u y))
    (dH : ∀u,VectorHeatDatum (fun y => Real.exp (V u y)))
    (hAB : ∀u∈S,HasDerivAt A (B u) u) (C R K L : ℝ≥0)
    (hA : ∀u∈S,‖A u‖ ≤ K) (hB : ∀u∈S,‖B u‖ ≤ L)
    (hfirstF : ∀u∈S,∀y,‖fderiv ℝ (fun z => Real.exp (V u z)*F u z) y‖ ≤ C*Real.exp (R*‖y‖))
    (hfirstH : ∀u∈S,∀y,‖fderiv ℝ (fun z => Real.exp (V u z)) y‖ ≤ C*Real.exp (R*‖y‖))
    (hpartialF : ∀u∈S,∀y,‖gaussianParameterDerivative (fun v z => Real.exp (V v z)*F v z) u y‖ ≤ C*Real.exp (R*‖y‖))
    (hpartialH : ∀u∈S,∀y,‖gaussianParameterDerivative (fun v z => Real.exp (V v z)) u y‖ ≤ C*Real.exp (R*‖y‖))
    (x : Field m) (c : ℝ) :
    HasDerivAt (fun u => gaussianLinearMean (fun y => Real.exp (V u y)*F u y) (A u) x-
      c*gaussianLinearMean (fun y => Real.exp (V u y)) (A u) x)
      (∫z,Real.exp (V a (x+A a z))*(
        gaussianExplicitCenteredScore V F a (x+A a z) c+
        ∑i : Fin n,gaussianScoreBilinear (V a) (F a) (x+A a z)
          (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1)) c)
        ∂fieldGaussian n) a := by
  let WF := fun u (y : Field m) => Real.exp (V u y)*F u y
  let WH := fun u (y : Field m) => Real.exp (V u y)
  have ha : a∈S := mem_of_mem_nhds hS
  have hWF (u) (hu : u∈S) (y) : DifferentiableAt ℝ (Function.uncurry WF) (u,y) :=
    (hV u hu y).exp.mul (hF u hu y)
  have hWH (u) (hu : u∈S) (y) : DifferentiableAt ℝ (Function.uncurry WH) (u,y) :=
    (hV u hu y).exp
  have hmWF : Measurable (gaussianParameterDerivative WF a) := by
    have he : gaussianParameterDerivative WF a = fun y =>
        Real.exp (V a y)*(gaussianParameterDerivative F a y+F a y*gaussianParameterDerivative V a y) := by
      funext y
      exact gaussianParameterDerivative_exp_mul V F (hV a ha y) (hF a ha y)
    rw [he]
    exact hVa.continuous.measurable.exp.mul
      (hmF.add (hFa.continuous.measurable.mul hmV))
  have hmWH : Measurable (gaussianParameterDerivative WH a) := by
    have he : gaussianParameterDerivative WH a = fun y =>
        Real.exp (V a y)*gaussianParameterDerivative V a y := by
      funext y
      exact gaussianParameterDerivative_exp V (hV a ha y)
    rw [he]
    exact hVa.continuous.measurable.exp.mul hmV
  have hpaF : AEStronglyMeasurable (fun z => gaussianParameterDerivative WF a (x+A a z)) (fieldGaussian n) :=
    (hmWF.comp (continuous_const.add (A a).continuous).measurable).aestronglyMeasurable
  have hpaH : AEStronglyMeasurable (fun z => gaussianParameterDerivative WH a (x+A a z)) (fieldGaussian n) :=
    (hmWH.comp (continuous_const.add (A a).continuous).measurable).aestronglyMeasurable
  have hdF := hasDerivAt_gaussianLinearParameterMean WF A B a S hS dF
    hWF hAB C R K L hA hB hfirstF hpartialF x hpaF
  have hdH := hasDerivAt_gaussianLinearParameterMean WH A B a S hS dH
    hWH hAB C R K L hA hB hfirstH hpartialH x hpaH
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
    gaussianExplicitCenteredScore_exp_identity V F (hV a ha _) (hF a ha _) c
  have hip : Integrable (fun z => Real.exp (V a (x+A a z))*gaussianExplicitCenteredScore V F a (x+A a z) c) (fieldGaussian n) := by
    simp_rw [he]
    exact hipF.sub (hipH.const_mul c)
  have his := integral_gaussian_centered_score (V a) (F a) hVa hFa
    (dF a) (dH a) (A a) (B a) x c
  apply (hdF.sub (hdH.const_mul c)).congr_deriv
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
  ring

end QuantitativeFollowup
