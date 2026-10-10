module
public import FourPapersCommon.FiniteStreamingClosedLimits
public import Mathlib.Topology.MetricSpace.UniformConvergence

@[expose] public section

/-! Genuine derivative convergence at the boundary of the interpolation interval.
Uniform derivative Cauchy estimates are derived by finite differences. -/
noncomputable section
open Set Filter
open scoped Topology NNReal
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem uniformCauchySeqOn_derivative_on_Icc (f D : ℕ → ℝ → ℝ)
    (hD : ∀ j z, z ∈ Icc (0 : ℝ) 1 → HasDerivWithinAt (f j) (D j z) (Icc 0 1) z)
    (L : ℝ≥0) (hL : ∀ j, LipschitzOnWith L (D j) (Icc 0 1))
    (hu : UniformCauchySeqOn f atTop (Icc 0 1)) :
    UniformCauchySeqOn D atTop (Icc 0 1) := by
  rw [Metric.uniformCauchySeqOn_iff] at hu ⊢
  intro ε hε
  let δ : ℝ := min (1/2) (ε/(8*(L+1)))
  have hδ : 0 < δ := by dsimp only [δ]; exact lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1/2 := min_le_left _ _
  have hδsmall : δ ≤ ε/(8*(L+1)) := min_le_right _ _
  obtain ⟨N, hN⟩ := hu (ε*δ/8) (by positivity)
  refine ⟨N, fun j hj k hk x hx => ?_⟩
  have hb (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) : |f j z - f k z| ≤ ε*δ/8 := by
    simpa only [Real.dist_eq] using (hN j hj k hk z hz).le
  have hd := derivative_sub_le_on_Icc (f j) (f k) (D j) (D k)
    (hD j) (hD k) L (hL j) (hL k) (ε*δ/8) hb δ hδ hδhalf x hx
  rw [Real.dist_eq]
  apply hd.trans_lt
  have he : 2*(ε*δ/8)/δ = ε/4 := by field_simp; ring
  rw [he]
  have hmul : δ*(8*(L+1)) ≤ ε := (le_div_iff₀ (by positivity)).mp hδsmall
  have hL0 := L.coe_nonneg
  nlinarith

theorem uniformCauchySeqOn_slopes_on_convex (f D : ℕ → ℝ → ℝ) (S : Set ℝ)
    (hS : Convex ℝ S)
    (hD : ∀ j z, z ∈ S → HasDerivWithinAt (f j) (D j z) S z)
    (hc : UniformCauchySeqOn D atTop S) (x : ℝ) (hx : x ∈ S) :
    UniformCauchySeqOn (fun j => slope (f j) x) atTop (S \ {x}) := by
  rw [Metric.uniformCauchySeqOn_iff] at hc ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε/2) (by positivity)
  refine ⟨N, fun j hj k hk y hy => ?_⟩
  have hdiff (z : ℝ) (hz : z ∈ S) :
      HasDerivWithinAt (fun w => f j w - f k w) (D j z - D k z) S z :=
    (hD j z hz).fun_sub (hD k z hz)
  have hb (z : ℝ) (hz : z ∈ S) : ‖D j z - D k z‖ ≤ ε/2 := by
    simpa only [Real.norm_eq_abs, Real.dist_eq] using (hN j hj k hk z hz).le
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hdiff hb hS hx hy.1
  have hyx : y ≠ x := by simpa only [mem_singleton_iff] using hy.2
  have hp : 0 < |y-x| := abs_pos.mpr (sub_ne_zero.mpr hyx)
  rw [Real.dist_eq, slope_def_field, slope_def_field, ← sub_div, abs_div]
  have he : (f j y-f j x)-(f k y-f k x) = (f j y-f k y)-(f j x-f k x) := by ring
  rw [he]
  apply lt_of_le_of_lt _ (by linarith : ε/2 < ε)
  exact (div_le_iff₀ hp).mpr (by simpa only [Real.norm_eq_abs] using hh)

theorem hasDerivWithinAt_of_uniform_derivative_limit_on_convex
    (f D : ℕ → ℝ → ℝ) (g d : ℝ → ℝ) (S : Set ℝ) (hS : Convex ℝ S)
    (hD : ∀ j z, z ∈ S → HasDerivWithinAt (f j) (D j z) S z)
    (hu : TendstoUniformlyOn D d atTop S)
    (hp : ∀ z ∈ S, Tendsto (fun j => f j z) atTop (𝓝 (g z)))
    (x : ℝ) (hx : x ∈ S) : HasDerivWithinAt g (d x) S x := by
  have hc := uniformCauchySeqOn_slopes_on_convex f D S hS hD hu.uniformCauchySeqOn x hx
  have ht (y : ℝ) (hy : y ∈ S \ {x}) :
      Tendsto (fun j => slope (f j) x y) atTop (𝓝 (slope g x y)) := by
    simpa only [slope_def_field] using ((hp y hy.1).sub (hp x hx)).div_const (y-x)
  have hs := hc.tendstoUniformlyOn_of_tendsto ht
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hsf := hs.tendstoUniformlyOnFilter.mono_right
    (show 𝓝[S \ {x}] x ≤ 𝓟 (S \ {x}) from inf_le_right)
  exact hsf.tendsto_of_eventually_tendsto
    (Eventually.of_forall fun j => hasDerivWithinAt_iff_tendsto_slope.mp (hD j x hx))
    (hu.tendsto_at hx)

end FourPapersCommon
