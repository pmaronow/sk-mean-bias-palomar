module
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

@[expose] public section

/-! A lower bound on the actual second derivative gives a midpoint gap.
Only interior differentiability and endpoint continuity are used; no
integrability or continuity of the second derivative is assumed. -/
noncomputable section
open Set
namespace FourPapersCommon

theorem midpoint_gap_of_second_derivative_lower (f f' f'' : ℝ → ℝ) (B : ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hB : ∀ x ∈ Ioo (0 : ℝ) 1, B ≤ f'' x) :
    B / 4 ≤ f 0 + f 1 - 2 * f (1 / 2) := by
  let g : ℝ → ℝ := fun x => f x - B / 2 * x ^ 2
  let g' : ℝ → ℝ := fun x => f' x - B * x
  have hgc : ContinuousOn g (Icc (0 : ℝ) 1) :=
    hf.sub (continuous_const.mul (continuous_id.pow 2)).continuousOn
  have hg : ConvexOn ℝ (Icc (0 : ℝ) 1) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := g')
      (f'' := fun x => f'' x - B) (convex_Icc 0 1) hgc
    · intro x hx
      rw [interior_Icc] at hx
      apply HasDerivAt.hasDerivWithinAt
      convert (hf' x hx).sub (((hasDerivAt_id x).pow 2).const_mul (B / 2)) using 1
      · funext y
        simp only [g, id_eq, Pi.sub_apply, Pi.pow_apply]
      · simp only [g', id_eq]
        ring
    · intro x hx
      rw [interior_Icc] at hx
      apply HasDerivAt.hasDerivWithinAt
      convert (hf'' x hx).sub ((hasDerivAt_id x).const_mul B) using 1
      · funext y
        rfl
      · simp only [mul_one]
    · intro x hx
      rw [interior_Icc] at hx
      exact sub_nonneg.mpr (hB x hx)
  have hm := hg.2 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  change g ((1 / 2) * 0 + (1 / 2) * 1) ≤ (1 / 2) * g 0 + (1 / 2) * g 1 at hm
  dsimp [g] at hm
  norm_num at hm
  linarith

theorem midpoint_minimum_gap_of_second_derivative_lower
    (f f' f'' : ℝ → ℝ) (B m : ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hB : ∀ x ∈ Ioo (0 : ℝ) 1, B ≤ f'' x)
    (hm : m ≤ f (1 / 2)) :
    B / 4 ≤ f 0 + f 1 - 2 * m := by
  linarith [midpoint_gap_of_second_derivative_lower f f' f'' B hf hf' hf'' hB]

end FourPapersCommon
