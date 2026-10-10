module
public import FourPapersCommon.VectorDriftTaylor
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section

/-! Actual first and second Frechet derivatives of a squared scalar test. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_square (f : E→ℝ) (hf : Differentiable ℝ f) (x : E) :
    fderiv ℝ (fun y=>f y^2) x=(2*f x) • fderiv ℝ f x := by
  have hh:=((hf x).hasFDerivAt.mul (hf x).hasFDerivAt).fderiv
  change fderiv ℝ (fun y=>f y*f y) x=_ at hh
  simp only [←pow_two] at hh
  rw [hh]
  ext u
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

theorem vectorHessian_square (f : E→ℝ) (hf : ContDiff ℝ 2 f) (x : E) :
    vectorHessian (fun y=>f y^2) x=
      (2 : ℝ) • (f x • vectorHessian f x+(fderiv ℝ f x).smulRight (fderiv ℝ f x)) := by
  have hd: Differentiable ℝ f:=hf.differentiable (by norm_num)
  have hD: Differentiable ℝ (fderiv ℝ f):=
    (hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have he : fderiv ℝ (fun y=>f y^2)=fun y=>(2 : ℝ) • (f y • fderiv ℝ f y) := by
    funext y
    rw [fderiv_square f hd]
    exact (smul_smul (2 : ℝ) (f y) (fderiv ℝ f y)).symm
  unfold vectorHessian
  rw [he]
  exact (((hd x).hasFDerivAt.smul (hD x).hasFDerivAt).const_smul (2 : ℝ)).fderiv

theorem vectorHessian_square_apply (f : E→ℝ) (hf : ContDiff ℝ 2 f)
    (x u v : E) :
    vectorHessian (fun y=>f y^2) x u v=
      2*f x*vectorHessian f x u v+2*fderiv ℝ f x u*fderiv ℝ f x v := by
  rw [vectorHessian_square f hf]
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

theorem norm_iteratedFDeriv_square_le (f : E→ℝ) (hf : ContDiff ℝ 3 f)
    (M : ℝ) (hM : 0≤M) (hb : ∀j,j≤3 → ∀x,‖iteratedFDeriv ℝ j f x‖≤M)
    (r : ℕ) (hr : r≤3) (x : E) :
    ‖iteratedFDeriv ℝ r (fun y=>f y^2) x‖≤2^r*M^2 := by
  have hh:=norm_iteratedFDeriv_mul_le hf hf x (show (r : ℕ∞ω)≤3 from by exact_mod_cast hr)
  simp only [←pow_two] at hh
  change ‖iteratedFDeriv ℝ r (fun y=>f y^2) x‖≤_ at hh
  refine hh.trans ?_
  calc
    _≤∑i∈Finset.range (r+1),(r.choose i : ℝ)*M*M := by
      apply Finset.sum_le_sum
      intro i hi
      have hir : i≤r:=by have:=Finset.mem_range.mp hi;omega
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hb i (hir.trans hr) x) (Nat.cast_nonneg _))
        (hb (r-i) (by omega) x) (norm_nonneg _) (by positivity)
    _=2^r*M^2 := by
      rw [←Finset.sum_mul,←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose,Nat.cast_pow]
      norm_num [pow_two]
      ring

end FourPapersCommon
