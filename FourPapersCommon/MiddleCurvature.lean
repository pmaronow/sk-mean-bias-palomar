module
public import FourPapersCommon.MidpointCurvature

@[expose] public section

/-! Curvature restricted to the middle half contributes the exact 3/16
midpoint coefficient. The outer intervals use genuine convex tangent
inequalities; no curvature bound is imposed there. -/
noncomputable section
open Set
namespace FourPapersCommon
set_option maxHeartbeats 1200000

theorem midpoint_gap_of_middle_curvature (f f' f'' : ℝ → ℝ) (B : ℝ)
    (hConvex : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀x∈Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀x∈Ioo (1/4 : ℝ) (3/4), HasDerivAt f' (f'' x) x)
    (hB : ∀x∈Ioo (1/4 : ℝ) (3/4), B ≤ f'' x) :
    3*B/16 ≤ f 0+f 1-2*f (1/2) := by
  let g : ℝ → ℝ := fun x => f x-B/2*x^2
  let g' : ℝ → ℝ := fun x => f' x-B*x
  have hSub : Icc (1/4 : ℝ) (3/4) ⊆ Icc (0 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hSubOpen : Icc (1/4 : ℝ) (3/4) ⊆ Ioo (0 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1,hx.2]
  have hg' : ∀x∈Icc (1/4 : ℝ) (3/4), HasDerivAt g (g' x) x := by
    intro x hx
    convert (hf' x (hSubOpen hx)).sub (((hasDerivAt_id x).pow 2).const_mul (B/2)) using 1
    · funext y
      rfl
    · dsimp only [g',id_eq]
      ring
  have hg : ConvexOn ℝ (Icc (1/4 : ℝ) (3/4)) g := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f':=g') (f'':=fun x => f'' x-B)
      (convex_Icc _ _) ((hf.mono hSub).sub (continuous_const.mul (continuous_id.pow 2)).continuousOn)
    · intro x hx
      rw [interior_Icc] at hx
      exact (hg' x ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      apply HasDerivAt.hasDerivWithinAt
      convert! (hf'' x hx).sub ((hasDerivAt_id x).const_mul B) using 1
      simp only [mul_one]
    · intro x hx
      rw [interior_Icc] at hx
      exact sub_nonneg.mpr (hB x hx)
  have hQuarter : (1/4 : ℝ) ∈ Icc (1/4 : ℝ) (3/4) := by norm_num
  have hThreeQuarter : (3/4 : ℝ) ∈ Icc (1/4 : ℝ) (3/4) := by norm_num
  have hMid := hg.2 hQuarter hThreeQuarter
    (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2)
    (by norm_num : (1/2 : ℝ)+1/2=1)
  change g ((1/2)*(1/4)+(1/2)*(3/4)) ≤ (1/2)*g (1/4)+(1/2)*g (3/4) at hMid
  dsimp only [g] at hMid
  norm_num at hMid
  have hD := hg.monotoneOn_deriv (fun x hx => (hg' x hx).differentiableAt)
    hQuarter hThreeQuarter (by norm_num : (1/4 : ℝ)≤3/4)
  rw [(hg' _ hQuarter).deriv,(hg' _ hThreeQuarter).deriv] at hD
  dsimp only [g'] at hD
  have hLeft := hConvex.slope_le_of_hasDerivAt (by norm_num : (0 : ℝ)∈Icc 0 1)
    (by norm_num : (1/4 : ℝ)∈Icc 0 1) (by norm_num : (0 : ℝ)<1/4)
    (hf' (1/4) (by norm_num))
  have hRight := hConvex.le_slope_of_hasDerivAt (by norm_num : (3/4 : ℝ)∈Icc 0 1)
    (by norm_num : (1 : ℝ)∈Icc 0 1) (by norm_num : (3/4 : ℝ)<1)
    (hf' (3/4) (by norm_num))
  simp only [slope_def_field] at hLeft hRight
  norm_num at hLeft hRight
  linarith

theorem midpoint_minimum_gap_of_middle_curvature (f f' f'' : ℝ → ℝ) (B m : ℝ)
    (hConvex : ConvexOn ℝ (Icc (0 : ℝ) 1) f)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀x∈Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀x∈Ioo (1/4 : ℝ) (3/4), HasDerivAt f' (f'' x) x)
    (hB : ∀x∈Ioo (1/4 : ℝ) (3/4), B ≤ f'' x)
    (hm : m ≤ f (1/2)) :
    3*B/16 ≤ f 0+f 1-2*m := by
  linarith [midpoint_gap_of_middle_curvature f f' f'' B hConvex hf hf' hf'' hB]

end FourPapersCommon
