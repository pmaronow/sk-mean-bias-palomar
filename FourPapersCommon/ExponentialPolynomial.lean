module
public import FourPapersCommon.ExponentialSmoothAlgebra
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

/-! Actual all-order exponential jet bounds are closed under polynomial
evaluation. The proof uses genuine bounded multilinear product estimates. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1800000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ExponentialSmoothOn.pow {f : E→ℝ} {s : Set E}
    (hf : ExponentialSmoothOn f s) (n : ℕ) :
    ExponentialSmoothOn (fun x=>f x^n) s:=by
  induction n with
  | zero => simpa only [pow_zero] using ExponentialSmoothOn.const (1:ℝ) s
  | succ n ih =>
    simpa only [pow_succ,ContinuousLinearMap.mul_apply'] using
      ih.bilinear hf (ContinuousLinearMap.mul ℝ ℝ)

theorem ExponentialSmoothOn.polynomial {f : E→ℝ} {s : Set E}
    (hf : ExponentialSmoothOn f s) (P : Polynomial ℝ) :
    ExponentialSmoothOn (fun x=>P.eval (f x)) s:=by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [Polynomial.eval_add] using hP.add hQ
  | monomial n a =>
    simpa only [Polynomial.eval_monomial,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply,smul_eq_mul,Function.comp_def] using
      (hf.pow n).compCLM (a • ContinuousLinearMap.id ℝ ℝ)

end FourPapersCommon
