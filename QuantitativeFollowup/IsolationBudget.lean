module
public import FourPapersCommon.MidpointCurvature
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

@[expose] public section

/-! Deterministic final step of isolation. The trial budget and second
derivative bound are explicit inputs here; the functional response and
level-set estimates must be instantiated separately for the actual model. -/
noncomputable section
open Set
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000

def isolationScale (β L c : ℝ) : ℝ :=
  min (1 / (2 * β ^ 2)) (min (1 / (β * L)) (3 * c / (2 * β)))

theorem isolationScale_pos (β L c : ℝ) (hβ : 0 < β) (hL : 0 < L) (hc : 0 < c) :
    0 < isolationScale β L c := by
  unfold isolationScale
  exact lt_min (by positivity) (lt_min (by positivity) (by positivity))

theorem isolationScale_bounds (β L c : ℝ) (hβ : 1 ≤ β) (hL : 1 ≤ L) (hc : 0 < c) :
    isolationScale β L c ≤ 1 ∧
      2 * β ^ 2 * isolationScale β L c ≤ 1 ∧
      β * L * isolationScale β L c ≤ 1 ∧
      β * (isolationScale β L c) ^ 2 / 12 ≤ c * isolationScale β L c / 8 := by
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hpos := isolationScale_pos β L c hβp hLp hc
  have h₁ := min_le_left (1 / (2 * β ^ 2)) (min (1 / (β * L)) (3 * c / (2 * β)))
  have h₂ := (min_le_right (1 / (2 * β ^ 2))
    (min (1 / (β * L)) (3 * c / (2 * β)))).trans (min_le_left _ _)
  have h₃ := (min_le_right (1 / (2 * β ^ 2))
    (min (1 / (β * L)) (3 * c / (2 * β)))).trans (min_le_right _ _)
  change isolationScale β L c ≤ 1 / (2 * β ^ 2) at h₁
  change isolationScale β L c ≤ 1 / (β * L) at h₂
  change isolationScale β L c ≤ 3 * c / (2 * β) at h₃
  have ha := (le_div_iff₀ (show 0 < 2 * β ^ 2 by positivity)).mp h₁
  have hb := (le_div_iff₀ (mul_pos hβp hLp)).mp h₂
  have hd := (le_div_iff₀ (show 0 < 2 * β by positivity)).mp h₃
  refine ⟨?_, by nlinarith, by nlinarith, ?_⟩
  · have hx : 2 * β ^ 2 ≥ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hx hpos.le]
  · nlinarith [mul_le_mul_of_nonneg_right hd hpos.le]

theorem isolation_smoothing_scale_admissible (β L c rho D : ℝ)
    (hβ : 1 ≤ β) (hL : 1 ≤ L) (hc : 0 < c)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (hD : D ∈ Ioc (0 : ℝ) β) :
    let h := isolationScale β L c * rho * D ^ 2
    0 < h ∧ h ≤ 1 / 2 ∧ 2 * β * h ≤ D ∧ h ≤ β / L := by
  let c₄ := isolationScale β L c
  have hβp : 0 < β := zero_lt_one.trans_le hβ
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hc₄ : 0 < c₄ := isolationScale_pos β L c hβp hLp hc
  have hb := isolationScale_bounds β L c hβ hL hc
  have hh₁ : c₄ * rho * D ^ 2 ≤ c₄ * D ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hrho.2 (mul_nonneg hc₄.le (sq_nonneg D))]
  have hh₂ : c₄ * D ^ 2 ≤ c₄ * β ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith [hD.1, hD.2]) hc₄.le
  have hh₃ : c₄ * D ^ 2 ≤ (c₄ * β) * D := by
    have hh := mul_le_mul_of_nonneg_left (show D ^ 2 ≤ β * D by nlinarith [hD.1, hD.2]) hc₄.le
    convert hh using 1
    ring
  refine ⟨mul_pos (mul_pos hc₄ hrho.1) (sq_pos_of_pos hD.1), ?_, ?_, ?_⟩
  · change c₄ * rho * D ^ 2 ≤ 1 / 2
    nlinarith [hb.2.1]
  · change 2 * β * (c₄ * rho * D ^ 2) ≤ D
    have hm := mul_le_mul_of_nonneg_right hb.2.1 hD.1.le
    have hh := mul_le_mul_of_nonneg_left (hh₁.trans hh₃) (show 0 ≤ 2 * β by positivity)
    nlinarith
  · change c₄ * rho * D ^ 2 ≤ β / L
    have hh₄ : c₄ * β ^ 2 ≤ β / L := by
      apply (le_div_iff₀ hLp).mpr
      have hm := mul_le_mul_of_nonneg_right hb.2.2.1 hβp.le
      nlinarith
    exact (hh₁.trans hh₂).trans hh₄

theorem isolation_budget_of_second_derivative (β L c rho D eta m : ℝ)
    (hβ : 1 ≤ β) (hL : 1 ≤ L) (hc : 0 < c)
    (hrho : rho ∈ Ioc (0 : ℝ) 1) (hD : D ∈ Ioc (0 : ℝ) β)
    (f f' f'' : ℝ → ℝ)
    (hf : ContinuousOn f (Icc (0 : ℝ) 1))
    (hf' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f (f' x) x)
    (hf'' : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt f' (f'' x) x)
    (hcurv : ∀ x ∈ Ioo (0 : ℝ) 1,
      c * rho ^ 2 * min (rho * D ^ 4)
        ((isolationScale β L c * rho * D ^ 2) * D ^ 2) ≤ f'' x)
    (hmin : m ≤ f (1 / 2))
    (hbudget : f 0 + f 1 - 2 * m ≤
      rho * β * (isolationScale β L c * rho * D ^ 2) ^ 2 / 12 + eta) :
    c * isolationScale β L c / 8 * rho ^ 3 * D ^ 4 ≤ eta := by
  let c₄ := isolationScale β L c
  have hb := isolationScale_bounds β L c hβ hL hc
  have hnonneg : 0 ≤ rho * D ^ 4 := mul_nonneg hrho.1.le (by positivity)
  have hsmall : (c₄ * rho * D ^ 2) * D ^ 2 ≤ rho * D ^ 4 := by
    have hm := mul_le_mul_of_nonneg_right hb.1 hnonneg
    nlinarith
  have he : c * rho ^ 2 * min (rho * D ^ 4) ((c₄ * rho * D ^ 2) * D ^ 2) =
      c * c₄ * rho ^ 3 * D ^ 4 := by
    rw [min_eq_right hsmall]
    ring
  have hc' : ∀ x ∈ Ioo (0 : ℝ) 1, c * c₄ * rho ^ 3 * D ^ 4 ≤ f'' x := by
    intro x hx
    exact he ▸ hcurv x hx
  have hg := FourPapersCommon.midpoint_minimum_gap_of_second_derivative_lower
    f f' f'' (c * c₄ * rho ^ 3 * D ^ 4) m hf hf' hf'' hc' hmin
  have hm := mul_le_mul_of_nonneg_right hb.2.2.2
    (mul_nonneg (pow_nonneg hrho.1.le 3) (pow_nonneg hD.1.le 4))
  have hecost : rho * β * (c₄ * rho * D ^ 2) ^ 2 / 12 =
      (β * c₄ ^ 2 / 12) * (rho ^ 3 * D ^ 4) := by ring
  rw [hecost] at hbudget
  nlinarith

end QuantitativeFollowup
