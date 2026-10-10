module
public import QuantitativePaper.VectorHeatStein

@[expose] public section

/-! Gaussian covariance differentiation for an actual observable, rather than
only for a log-partition potential. The growth hypotheses are genuine analytic
bounds; the integration-by-parts conclusion is obtained from the Gaussian law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def gaussianLinearFirst (F : Field m → ℝ) (A B : Field n →L[ℝ] Field m)
    (x : Field m) (i : Fin n) (z : Field n) : ℝ :=
  fderiv ℝ F (x+A z) (B (EuclideanSpace.single i 1))

 theorem hasFDerivAt_gaussianLinearFirst {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : Field n →L[ℝ] Field m) (x : Field m) (i : Fin n) (z : Field n) :
    HasFDerivAt (gaussianLinearFirst F A B x i)
      (((vectorHessian F (x+A z)).flip (B (EuclideanSpace.single i 1))).comp A) z := by
  have hdF := (d.regularity.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hdg : HasFDerivAt (fun y => fderiv ℝ F y (B (EuclideanSpace.single i 1)))
      ((vectorHessian F (x+A z)).flip (B (EuclideanSpace.single i 1))) (x+A z) := by
    simpa only [ContinuousLinearMap.comp_zero,zero_add,vectorHessian] using
      (hdF (x+A z)).hasFDerivAt.clm_apply (hasFDerivAt_const (B (EuclideanSpace.single i 1)) (x+A z))
  have hshift : HasFDerivAt (fun w => x+A w) A z := by
    simpa only [zero_add] using (hasFDerivAt_const x z).fun_add A.hasFDerivAt
  exact hdg.comp z hshift

 theorem gaussianLinearFirst_growth {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : Field n →L[ℝ] Field m) (x : Field m) (i : Fin n) :
    let K := (1+‖A‖)*‖B‖*d.growthBound*Real.exp (d.rate*‖x‖)
    let c := d.rate*‖A‖
    (∀ z,|gaussianLinearFirst F A B x i z| ≤ K*Real.exp (c*‖z‖)) ∧
      (∀ z,‖gradient (gaussianLinearFirst F A B x i) z‖ ≤ K*Real.exp (c*‖z‖)) := by
  have he : ‖EuclideanSpace.single i (1 : ℝ)‖=1 := by simp
  have hn (z : Field n) : ‖x+A z‖ ≤ ‖x‖+‖A‖*‖z‖ :=
    (norm_add_le _ _).trans (add_le_add le_rfl (A.le_opNorm z))
  have hg (z : Field n) : d.growthBound*Real.exp (d.rate*‖x+A z‖) ≤
      d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*‖A‖)*‖z‖) := by
    have hh := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hn z) d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    simpa only [mul_add,Real.exp_add,mul_assoc] using hh
  have hb : ‖B (EuclideanSpace.single i 1)‖ ≤ ‖B‖ := by simpa only [he,mul_one] using B.le_opNorm (EuclideanSpace.single i 1)
  constructor
  · intro z
    have ht := (fderiv ℝ F (x+A z)).le_opNorm (B (EuclideanSpace.single i 1))
    change |gaussianLinearFirst F A B x i z| ≤ _
    change ‖fderiv ℝ F (x+A z) (B (EuclideanSpace.single i 1))‖ ≤ _
    apply ht.trans
    have hbd := mul_le_mul ((d.first_bound _).trans (hg z)) hb (norm_nonneg _) (by positivity)
    apply hbd.trans
    have hp : 0 ≤ ‖B‖*d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*‖A‖)*‖z‖) := by positivity
    nlinarith [mul_nonneg (norm_nonneg A) hp]
  · intro z
    have hnG : ‖gradient (gaussianLinearFirst F A B x i) z‖=‖fderiv ℝ (gaussianLinearFirst F A B x i) z‖ := by
      rw [gradient]
      exact LinearIsometryEquiv.norm_map _ _
    rw [hnG,(hasFDerivAt_gaussianLinearFirst d A B x i z).fderiv]
    have hf := ((vectorHessian F (x+A z)).flip).le_opNorm (B (EuclideanSpace.single i 1))
    rw [ContinuousLinearMap.opNorm_flip] at hf
    have hcomp := ContinuousLinearMap.opNorm_comp_le
      (h := (vectorHessian F (x+A z)).flip (B (EuclideanSpace.single i 1))) A
    have hs : ‖((vectorHessian F (x+A z)).flip (B (EuclideanSpace.single i 1))).comp A‖ ≤
        (d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*‖A‖)*‖z‖))*‖B‖*‖A‖ := by
      apply hcomp.trans
      exact mul_le_mul_of_nonneg_right
        ((hf.trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))).trans
          (mul_le_mul_of_nonneg_right ((d.second_bound _).trans (hg z)) (norm_nonneg B))) (norm_nonneg A)
    apply hs.trans
    have hp : 0 ≤ ‖B‖*d.growthBound*Real.exp (d.rate*‖x‖)*Real.exp ((d.rate*‖A‖)*‖z‖) := by positivity
    nlinarith

 theorem gaussianLinearFirst_stein {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : Field n →L[ℝ] Field m) (x : Field m) (i : Fin n) :
    Integrable (fun z => z i*gaussianLinearFirst F A B x i z) (fieldGaussian n) ∧
    Integrable (fun z => vectorHessian F (x+A z) (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1))) (fieldGaussian n) ∧
    (∫ z,z i*gaussianLinearFirst F A B x i z ∂fieldGaussian n)=
      ∫ z,vectorHessian F (x+A z) (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) ∂fieldGaussian n := by
  have hshift : ContDiff ℝ 1 (fun z : Field n => x+A z) := contDiff_const.add A.contDiff
  have hs : ContDiff ℝ 1 (gaussianLinearFirst F A B x i) :=
    ((d.regularity.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).comp hshift
  have hg := gaussianLinearFirst_growth d A B x i
  let K := (1+‖A‖)*‖B‖*d.growthBound*Real.exp (d.rate*‖x‖)
  let c := d.rate*‖A‖
  have hint := SYK.gaussian_ibp_integrable (gaussianLinearFirst F A B x i) i hs K c hg.1 hg.2
  have he (z : Field n) : gradient (gaussianLinearFirst F A B x i) z i=
      vectorHessian F (x+A z) (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) := by
    rw [SYK.gradient_coord_eq,(hasFDerivAt_gaussianLinearFirst d A B x i z).fderiv]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.flip_apply]
  refine ⟨hint.1,?_,?_⟩
  · simpa only [he] using hint.2
  · have hh := SYK.gaussian_ibp_coord (gaussianLinearFirst F A B x i) i hs K c hg.1 hg.2
    change (∫ z,z i*gaussianLinearFirst F A B x i z ∂fieldGaussian n)=∫ z,gradient (gaussianLinearFirst F A B x i) z i ∂fieldGaussian n at hh
    simpa only [he] using hh

 theorem integral_gaussianLinear_covariance_response {F : Field m → ℝ} (d : VectorHeatDatum F)
    (A B : Field n →L[ℝ] Field m) (x : Field m) :
    Integrable (fun z => fderiv ℝ F (x+A z) (B z)) (fieldGaussian n) ∧
    (∫ z,fderiv ℝ F (x+A z) (B z) ∂fieldGaussian n)=
      ∫ z,∑ i : Fin n,vectorHessian F (x+A z) (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1)) ∂fieldGaussian n := by
  have he (z : Field n) : fderiv ℝ F (x+A z) (B z)=∑ i : Fin n,z i*gaussianLinearFirst F A B x i z := by
    have he := field_clm_basis_expansion ((fderiv ℝ F (x+A z)).comp B) z
    simpa only [ContinuousLinearMap.comp_apply,EuclideanSpace.basisFun_apply,gaussianLinearFirst] using he
  have hs (i : Fin n) := gaussianLinearFirst_stein d A B x i
  constructor
  · simp_rw [he]
    exact integrable_finsetSum _ (fun i _ => (hs i).1)
  · simp_rw [he]
    rw [integral_finsetSum _ (fun i _ => (hs i).1),integral_finsetSum _ (fun i _ => (hs i).2.1)]
    exact Finset.sum_congr rfl (fun i _ => (hs i).2.2)

end QuantitativeFollowup
