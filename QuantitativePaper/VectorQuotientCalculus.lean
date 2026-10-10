module
public import QuantitativePaper.VectorGaussianHeatPDE
public import QuantitativeFollowup.DirectionalConvexity

@[expose] public section

/-! Literal directional first and second derivatives of a vector scalar
quotient. These identities will give the normalized heat generator. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorQuotientFirst (f g : Field n → ℝ) (x w : Field n) : ℝ :=
  (fderiv ℝ f x w*g x-f x*fderiv ℝ g x w)/(g x)^2

def vectorQuotientSecond (f g : Field n → ℝ) (x w : Field n) : ℝ :=
  vectorHessian f x w w/g x-
    2*fderiv ℝ f x w*fderiv ℝ g x w/(g x)^2-
    f x*vectorHessian g x w w/(g x)^2+
    2*f x*(fderiv ℝ g x w)^2/(g x)^3

theorem fderiv_vectorQuotient_apply (f g : Field n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hne : ∀ x,g x≠0)
    (x w : Field n) : fderiv ℝ (fun y=>f y/g y) x w=vectorQuotientFirst f g x w := by
  have hq : ContDiff ℝ 2 (fun y=>f y/g y) := hf.div hg hne
  have h1 := hasDerivAt_on_affine_line (fun y=>f y/g y) hq x w 0
  have h2 := (hasDerivAt_on_affine_line f hf x w 0).div
    (hasDerivAt_on_affine_line g hg x w 0) (by simpa only [zero_smul,add_zero] using hne x)
  have hh := h1.unique h2
  simpa only [zero_smul,add_zero,vectorQuotientFirst] using hh

theorem vectorHessian_vectorQuotient_apply (f g : Field n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hne : ∀ x,g x≠0)
    (x w : Field n) :
    vectorHessian (fun y=>f y/g y) x w w=vectorQuotientSecond f g x w := by
  have hq : ContDiff ℝ 2 (fun y=>f y/g y) := hf.div hg hne
  have he : (fun t : ℝ=>fderiv ℝ (fun y=>f y/g y) (x+t • w) w)=
      fun t=>vectorQuotientFirst f g (x+t • w) w :=
    funext fun t=>fderiv_vectorQuotient_apply f g hf hg hne _ w
  have hq1 := hasDerivAt_directional_on_affine_line (fun y=>f y/g y) hq x w 0
  rw [he] at hq1
  have hf0 := hasDerivAt_on_affine_line f hf x w 0
  have hg0 := hasDerivAt_on_affine_line g hg x w 0
  have hf1 := hasDerivAt_directional_on_affine_line f hf x w 0
  have hg1 := hasDerivAt_directional_on_affine_line g hg x w 0
  have hnum := (hf1.mul hg0).sub (hf0.mul hg1)
  have hden := hg0.pow 2
  have hd := hnum.div hden (by simpa only [Pi.pow_apply,zero_smul,add_zero] using pow_ne_zero 2 (hne x))
  change HasDerivAt (fun t=>vectorQuotientFirst f g (x+t • w) w) _ 0 at hd
  have hh := hq1.unique hd
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.sub_apply,zero_smul,add_zero,directionalHessian] at hh
  change vectorHessian (fun y=>f y/g y) x w w=_ at hh
  rw [hh]
  unfold vectorQuotientSecond vectorHessian
  field_simp [hne x] <;> ring

theorem vector_quotient_generator (f g : Field n → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hne : ∀ x,g x≠0) (x : Field n) :
    vectorBilinearTrace (vectorHessian (fun y=>f y/g y) x)/2+
      fderiv ℝ (fun y=>f y/g y) x ((g x)⁻¹ • gradient g x)=
      vectorBilinearTrace (vectorHessian f x)/(2*g x)-
        f x*vectorBilinearTrace (vectorHessian g x)/(2*(g x)^2) := by
  have hgD := field_clm_basis_expansion (fderiv ℝ (fun y=>f y/g y) x) ((g x)⁻¹ • gradient g x)
  simp only [PiLp.smul_apply,smul_eq_mul,EuclideanSpace.basisFun_apply,SYK.gradient_coord_eq] at hgD
  rw [hgD]
  unfold vectorBilinearTrace
  simp_rw [vectorHessian_vectorQuotient_apply f g hf hg hne,
    fderiv_vectorQuotient_apply f g hf hg hne]
  rw [Finset.sum_div,Finset.sum_div,Finset.mul_sum,Finset.sum_div,
    ← Finset.sum_sub_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold vectorQuotientSecond vectorQuotientFirst
  field_simp [hne x] <;> ring

end QuantitativePaper
