module
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Tactic

@[expose] public section

/-! A slope-uniform approximation transfers genuine one-sided derivatives.
This is useful for truncating integrable unbounded initial weights. -/
noncomputable section
open Set Filter
open scoped Topology
namespace FourPapersCommon

theorem hasDerivWithinAt_zero_of_uniform_increment_approximation
    (f : ℝ → ℝ) (F : ℕ → ℝ → ℝ) (d : ℝ) (D error : ℕ → ℝ) (s : Set ℝ)
    (hF : ∀k,HasDerivWithinAt (F k) (D k) s 0)
    (hD : Tendsto D atTop (𝓝 d)) (he : Tendsto error atTop (𝓝 0))
    (hb : ∀k,∀r ∈ s,‖(F k r-F k 0)-(f r-f 0)‖ ≤ error k*‖r‖) :
    HasDerivWithinAt f d s 0 := by
  have hu : TendstoUniformlyOn (fun k => slope (F k) 0) (slope f 0) atTop (s\{0}) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [he.eventually (gt_mem_nhds hε)] with k hk
    intro r hr
    have hr0 : r ≠ 0 := by simpa only [mem_singleton_iff] using hr.2
    have hh := hb k r hr.1
    rw [Real.dist_eq,slope_def_field,slope_def_field,sub_zero,← sub_div,abs_div]
    apply lt_of_le_of_lt _ hk
    apply (div_le_iff₀ (abs_pos.mpr hr0)).mpr
    simpa only [Real.norm_eq_abs,abs_sub_comm] using hh
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have huf := hu.tendstoUniformlyOnFilter.mono_right
    (show 𝓝[s\{0}] (0 : ℝ) ≤ 𝓟 (s\{0}) from inf_le_right)
  exact huf.tendsto_of_eventually_tendsto
    (Eventually.of_forall (fun k => hasDerivWithinAt_iff_tendsto_slope.mp (hF k))) hD

end FourPapersCommon
