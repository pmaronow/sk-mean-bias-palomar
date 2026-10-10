module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

/-! Genuine all-order bounded jets of Fourier test functions on real
Banach spaces, obtained from the actual scalar sine and cosine derivatives. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
set_option maxHeartbeats 1000000
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedDeriv_sin_cos_le_one (j : ℕ) (x : ℝ) :
    ‖iteratedDeriv j Real.sin x‖≤1 ∧ ‖iteratedDeriv j Real.cos x‖≤1 := by
  induction j with
  | zero=>simpa only [iteratedDeriv_zero,Real.norm_eq_abs] using
      And.intro (Real.abs_sin_le_one x) (Real.abs_cos_le_one x)
  | succ j ih=>
    constructor
    · rw [Real.iteratedDeriv_add_one_sin]
      exact ih.2
    · rw [Real.iteratedDeriv_add_one_cos]
      simpa only [Pi.neg_apply,norm_neg] using ih.1

theorem norm_iteratedFDeriv_sin_clm_le (L : E→L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y=>Real.sin (L y)) x‖≤‖L‖^j := by
  have hS : ContDiff ℝ j Real.sin := Real.contDiff_sin
  change ‖iteratedFDeriv ℝ j (Real.sin ∘ L) x‖≤‖L‖^j
  rw [L.iteratedFDeriv_comp_right hS x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (mul_le_mul_of_nonneg_right (norm_iteratedDeriv_sin_cos_le_one j (L x)).1
    (pow_nonneg (norm_nonneg L) j)).trans_eq (one_mul _)

theorem norm_iteratedFDeriv_cos_clm_le (L : E→L[ℝ] ℝ) (j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ j (fun y=>Real.cos (L y)) x‖≤‖L‖^j := by
  have hS : ContDiff ℝ j Real.cos := Real.contDiff_cos
  change ‖iteratedFDeriv ℝ j (Real.cos ∘ L) x‖≤‖L‖^j
  rw [L.iteratedFDeriv_comp_right hS x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  exact (mul_le_mul_of_nonneg_right (norm_iteratedDeriv_sin_cos_le_one j (L x)).2
    (pow_nonneg (norm_nonneg L) j)).trans_eq (one_mul _)

end FourPapersCommon
