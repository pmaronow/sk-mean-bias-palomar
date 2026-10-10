module
public import Mathlib.Analysis.Calculus.TaylorIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! A genuine uniform cubic bound for the second-order Taylor remainder in
an arbitrary real normed field space. It supplies the finite partition Itô
expectation proof without a stochastic formula assumption. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Nat
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorSecondTaylorPolynomial (f : E → ℝ) (x y : E) : ℝ :=
  f x+fderiv ℝ f x y+(1/2:ℝ)*iteratedFDeriv ℝ 2 f x (fun _=>y)

theorem vector_second_taylor_cubic_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {K : ℝ} (hK : 0 ≤ K) (hbound : ∀ x,‖iteratedFDeriv ℝ 3 f x‖ ≤ K) (x y : E) :
    |f (x+y)-vectorSecondTaylorPolynomial f x y| ≤ K/2*‖y‖^3 := by
  let R : ℝ → ℝ := fun u=>(1-u)^2*iteratedFDeriv ℝ 3 f (x+u • y) (fun _=>y)
  have H := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (x := x) (y := y)
    (fun u hu=>hf.contDiffAt)
  have he : f (x+y)-vectorSecondTaylorPolynomial f x y=(1/2:ℝ)*(∫ u in (0:ℝ)..1,R u) := by
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
      Nat.factorial_zero,Nat.factorial_one,Nat.factorial_two,Nat.cast_one,Nat.cast_ofNat,
      inv_one,one_smul,iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,smul_eq_mul] at H
    dsimp only [vectorSecondTaylorPolynomial,R]
    linarith only [H]
  have hb (u : ℝ) (hu : u∈uIcc (0:ℝ) 1) : ‖R u‖ ≤ K*‖y‖^3 := by
    rw [uIcc_of_le zero_le_one] at hu
    have ht : ‖iteratedFDeriv ℝ 3 f (x+u • y) (fun _=>y)‖ ≤ K*‖y‖^3 := by
      calc
        _ ≤ ‖iteratedFDeriv ℝ 3 f (x+u • y)‖*∏ i : Fin 3,‖y‖ :=
          (iteratedFDeriv ℝ 3 f (x+u • y)).le_opNorm _
        _ ≤ K*‖y‖^3 := by
          simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
          exact mul_le_mul_of_nonneg_right (hbound _) (by positivity)
    have hw : (1-u)^2 ≤ 1 := by nlinarith [hu.1,hu.2]
    calc
      _ = (1-u)^2*‖iteratedFDeriv ℝ 3 f (x+u • y) (fun _=>y)‖ := by
        dsimp only [R]
        rw [norm_mul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      _ ≤ 1*(K*‖y‖^3) := mul_le_mul hw ht (norm_nonneg _) (by positivity)
      _ = _ := one_mul _
  have HI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 1) (f := R) (fun u hu=>hb u (uIoc_subset_uIcc hu))
  rw [he,abs_mul,show |(1/2:ℝ)|=1/2 by norm_num]
  have Habs : |∫ u in (0:ℝ)..1,R u| ≤ K*‖y‖^3 := by
    simpa only [Real.norm_eq_abs,sub_zero,abs_one,mul_one] using HI
  nlinarith

end FourPapersCommon
