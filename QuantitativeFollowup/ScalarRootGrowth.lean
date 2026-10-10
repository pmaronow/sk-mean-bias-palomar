module
public import QuantitativeFollowup.ScalarRootStrictness
public import QuantitativeFollowup.ScalarDensity
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section

/-! Strict local linear growth of the actual minimizing CDF. This follows
from its genuine positive right derivative, not from a lower-bound premise. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB
open scoped Topology
namespace QuantitativeFollowup

theorem scalar_minimizer_cdf_linear_lower (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q) :
    ∃ k T : ℝ, 0<k ∧ T∈Ioo (0:ℝ) q ∧
      ∀ r∈Icc (0:ℝ) T, k*r≤β*parisiCDF μ r := by
  let ρ:=parisiSmoothDensity β μ q 0
  have hρ : 0<ρ := scalar_minimizer_root_density_pos β hβ μ hmin q hq hsupp
  have hd:=(momentQuotient_hasDerivAt_endpoints_of_support_interval
    β hβ.ne' μ hmin q hq.1 hq.2.le hsupp).1.Ioi_of_Ici
  have hl : Tendsto (slope (momentQuotient β μ) 0) (𝓝[>] 0) (𝓝 ρ) :=
    (hasDerivWithinAt_iff_tendsto_slope' (show (0:ℝ)∉Ioi (0:ℝ) from by simp)).mp hd
  have he : ∀ᶠr in 𝓝[>] (0:ℝ), ρ/2<slope (momentQuotient β μ) 0 r :=
    hl.eventually (eventually_gt_nhds (by linarith : ρ/2<ρ))
  obtain ⟨u,hu,hbound⟩:=mem_nhdsGT_iff_exists_Ioc_subset.mp he
  let T:=min u (q/2)
  have hT0 : 0<T := lt_min hu (half_pos hq.1)
  have hTq : T<q := (min_le_right u (q/2)).trans_lt (half_lt_self hq.1)
  refine ⟨β*(ρ/2),T,mul_pos hβ (half_pos hρ),⟨hT0,hTq⟩,?_⟩
  intro r hr
  by_cases hr0 : r=0
  · subst r
    simp only [mul_zero]
    exact mul_nonneg hβ.le (parisiCDF_nonneg μ 0)
  have hrp : 0<r := lt_of_le_of_ne hr.1 (Ne.symm hr0)
  have hs:=hbound ⟨hrp,hr.2.trans (min_le_left u (q/2))⟩
  have hc:=parisiCDF_eq_momentQuotient_on_support_interval
    β hβ.ne' μ hmin q hq.1 hq.2.le hsupp r ⟨hr.1,hr.2.trans_lt hTq⟩
  simp only [slope_def_field,momentQuotient_initial_zero,sub_zero] at hs
  have hb : ρ/2*r ≤ momentQuotient β μ r := ((lt_div_iff₀ hrp).mp hs).le
  rw [hc]
  nlinarith

theorem scalar_root_growth_uniform_minimizers (β : ℝ) (hβ : 1<β) :
    ∃ k T : ℝ, 0<k ∧ T∈Ioo (0:ℝ) 1 ∧
      ∀ μ : Paper.ParisiMeasure, IsParisiMinimizer β 0 μ →
        ∀ r∈Icc (0:ℝ) T, k*r≤β*parisiCDF μ r := by
  obtain ⟨q,hq,hsupp⟩:=minimizer_full_support β hβ (parisiMinimizer β 0)
    (isParisiMinimizer_selected β 0)
  obtain ⟨k,T,hk,hT,hbound⟩:=scalar_minimizer_cdf_linear_lower β
    (zero_lt_one.trans hβ) _ (isParisiMinimizer_selected β 0) q hq hsupp
  refine ⟨k,T,hk,⟨hT.1,hT.2.trans hq.2⟩,?_⟩
  intro μ hμ
  rw [parisiMinimizer_unique β (zero_lt_one.trans hβ).ne' μ hμ]
  exact hbound

end QuantitativeFollowup
