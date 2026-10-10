module
public import QuantitativeFollowup.GaussianWeightHessian

@[expose] public section

/-! The centered score formula for a normalized actual Gaussian observable.
The covariance changes through a genuine linear-input curve, and all
normalization and Gaussian integration by parts are proved. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

 def gaussianScoreBilinear (V F : Field m → ℝ) (x u v : Field m) (c : ℝ) : ℝ :=
  vectorHessian F x u v+fderiv ℝ V x u*fderiv ℝ F x v+fderiv ℝ V x v*fderiv ℝ F x u+
    (F x-c)*(vectorHessian V x u v+fderiv ℝ V x u*fderiv ℝ V x v)

 theorem gaussianScoreBilinear_exp_identity (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (x u v : Field m) (c : ℝ) :
    Real.exp (V x)*gaussianScoreBilinear V F x u v c=
      vectorHessian (fun y => Real.exp (V y)*F y) x u v-
        c*vectorHessian (fun y => Real.exp (V y)) x u v := by
  rw [vectorHessian_exp_mul_observable V F hV hF,vectorHessian_exp_potential V hV]
  unfold gaussianScoreBilinear
  ring

 theorem integral_gaussian_centered_score (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F)
    (dF : VectorHeatDatum (fun y => Real.exp (V y)*F y))
    (dH : VectorHeatDatum (fun y => Real.exp (V y)))
    (A B : Field n →L[ℝ] Field m) (x : Field m) (c : ℝ) :
    Integrable (fun z => Real.exp (V (x+A z))*∑ i : Fin n,gaussianScoreBilinear V F (x+A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) c) (fieldGaussian n) ∧
    (∫ z,Real.exp (V (x+A z))*∑ i : Fin n,gaussianScoreBilinear V F (x+A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) c ∂fieldGaussian n)=
    (∫ z,∑ i : Fin n,vectorHessian (fun y => Real.exp (V y)*F y) (x+A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) ∂fieldGaussian n)-
      c*(∫ z,∑ i : Fin n,vectorHessian (fun y => Real.exp (V y)) (x+A z)
        (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) ∂fieldGaussian n) := by
  have hsF (i : Fin n) := (gaussianLinearFirst_stein dF A B x i).2.1
  have hsH (i : Fin n) := (gaussianLinearFirst_stein dH A B x i).2.1
  have hiF := integrable_finsetSum Finset.univ (fun i _ => hsF i)
  have hiH := integrable_finsetSum Finset.univ (fun i _ => hsH i)
  have he : (fun z => Real.exp (V (x+A z))*∑ i : Fin n,gaussianScoreBilinear V F (x+A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) c)=
    (fun z => (∑ i : Fin n,vectorHessian (fun y => Real.exp (V y)*F y) (x+A z)
      (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)))-
      c*(∑ i : Fin n,vectorHessian (fun y => Real.exp (V y)) (x+A z)
        (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)))) := by
    funext z
    rw [Finset.mul_sum,Finset.mul_sum,←Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => gaussianScoreBilinear_exp_identity V F hV hF _ _ _ c)
  constructor
  · rw [he]
    exact hiF.sub (hiH.const_mul c)
  · rw [he,integral_sub hiF (hiH.const_mul c),integral_const_mul]

 theorem hasDerivAt_gaussian_weighted_covariance_response (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F)
    (dF : VectorHeatDatum (fun y => Real.exp (V y)*F y))
    (dH : VectorHeatDatum (fun y => Real.exp (V y)))
    (A B : ℝ → Field n →L[ℝ] Field m) (a : ℝ) (S : Set ℝ) (hS : S∈𝓝 a)
    (hAB : ∀ u∈S,HasDerivAt A (B u) u) (K L : ℝ) (hK : 0 ≤ K)
    (hA : ∀ u∈S,‖A u‖ ≤ K) (hB : ∀ u∈S,‖B u‖ ≤ L) (x : Field m)
    (hH : gaussianLinearMean (fun y => Real.exp (V y)) (A a) x ≠ 0) :
    HasDerivAt (fun u => gaussianLinearNormalizedMean (fun y => Real.exp (V y)*F y)
      (fun y => Real.exp (V y)) (A u) x)
      ((∫ z,Real.exp (V (x+A a z))*∑ i : Fin n,gaussianScoreBilinear V F (x+A a z)
        (A a (EuclideanSpace.single i 1)) (B a (EuclideanSpace.single i 1))
        (gaussianLinearNormalizedMean (fun y => Real.exp (V y)*F y) (fun y => Real.exp (V y)) (A a) x)
        ∂fieldGaussian n)/gaussianLinearMean (fun y => Real.exp (V y)) (A a) x) a := by
  have hd := hasDerivAt_gaussianLinearNormalizedMean dF dH A B a S hS hAB K L hK hA hB x hH
  apply hd.congr_deriv
  rw [(integral_gaussian_centered_score V F hV hF dF dH (A a) (B a) x _).2]
  unfold gaussianLinearNormalizedMean
  field_simp [hH]

end QuantitativeFollowup
