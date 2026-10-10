module
public import FourPapersCommon.VectorTaylorRemainder

@[expose] public section

/-! Actual second-order expansion separating the Gaussian increment from the
bounded drift increment. The error keeps the mixed terms needed to vanish in
the partition proof of the vector Itô expectation identity. -/
noncomputable section
open scoped ContDiff
namespace FourPapersCommon
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def vectorHessian (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  fderiv ℝ (fderiv ℝ f) x

theorem vectorHessian_norm_eq (f : E → ℝ) (x : E) :
    ‖vectorHessian f x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
  rw [vectorHessian, ← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]

theorem vectorHessian_apply_bound {f : E → ℝ} {x : E} {K : ℝ}
    (hK : ‖vectorHessian f x‖ ≤ K) (u v : E) :
    |vectorHessian f x u v| ≤ K*‖u‖*‖v‖ := by
  calc
    _ ≤ ‖vectorHessian f x u‖*‖v‖ := by
      simpa only [Real.norm_eq_abs] using (vectorHessian f x u).le_opNorm v
    _ ≤ (‖vectorHessian f x‖*‖u‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right ((vectorHessian f x).le_opNorm u) (norm_nonneg _)
    _ ≤ (K*‖u‖)*‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hK (norm_nonneg _)) (norm_nonneg _)

def vectorNoiseDriftTaylorPolynomial (f : E → ℝ) (x w v : E) : ℝ :=
  f x+fderiv ℝ f x w+fderiv ℝ f x v+(1/2:ℝ)*vectorHessian f x w w

theorem vector_noise_drift_taylor_bound {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {K₂ K₃ : ℝ} (hK₃ : 0 ≤ K₃)
    (h₂ : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖ ≤ K₂)
    (h₃ : ∀ x, ‖iteratedFDeriv ℝ 3 f x‖ ≤ K₃) (x w v : E) :
    |f (x+w+v)-vectorNoiseDriftTaylorPolynomial f x w v| ≤
      K₃/2*‖w+v‖^3+K₂*‖w‖*‖v‖+K₂/2*‖v‖^2 := by
  have hH : ‖vectorHessian f x‖ ≤ K₂ := by
    rw [vectorHessian_norm_eq]
    exact h₂ x
  have h₁ := vectorHessian_apply_bound hH w v
  have h₂' := vectorHessian_apply_bound hH v w
  have h₃' := vectorHessian_apply_bound hH v v
  have he : f (x+w+v)-vectorNoiseDriftTaylorPolynomial f x w v =
      (f (x+(w+v))-vectorSecondTaylorPolynomial f x (w+v))+
      (1/2:ℝ)*(vectorHessian f x w v+vectorHessian f x v w+
        vectorHessian f x v v) := by
    simp only [vectorNoiseDriftTaylorPolynomial,vectorSecondTaylorPolynomial,
      iteratedFDeriv_two_apply,map_add,ContinuousLinearMap.add_apply,vectorHessian]
    rw [add_assoc x w v]
    ring
  rw [he]
  calc
    _ ≤ |f (x+(w+v))-vectorSecondTaylorPolynomial f x (w+v)|+
        |(1/2:ℝ)*(vectorHessian f x w v+vectorHessian f x v w+
          vectorHessian f x v v)| := abs_add_le _ _
    _ ≤ K₃/2*‖w+v‖^3+
        (1/2:ℝ)*(|vectorHessian f x w v|+|vectorHessian f x v w|+
          |vectorHessian f x v v|) := by
      have hs := abs_add_le (vectorHessian f x w v+vectorHessian f x v w)
        (vectorHessian f x v v)
      have hs' := abs_add_le (vectorHessian f x w v) (vectorHessian f x v w)
      rw [abs_mul,show |(1/2:ℝ)|=1/2 by norm_num]
      have ht := vector_second_taylor_cubic_bound hf hK₃ h₃ x (w+v)
      nlinarith
    _ ≤ _ := by nlinarith

end FourPapersCommon
