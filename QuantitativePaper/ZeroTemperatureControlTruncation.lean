module
public import QuantitativePaper.ZeroTemperatureControlStability

@[expose] public section

/-! Actual L1 truncation of integrable nonnegative profiles and uniform
convergence of their canonical Brownian |x|-terminal control values. -/
noncomputable section
open Set MeasureTheory Filter Paper
open scoped Topology
namespace QuantitativePaper
set_option maxHeartbeats 500000

def zeroProfileTruncation (γ : ℝ→ℝ) (R : ℝ) (q : ℝ) : ℝ := min (max 0 (γ q)) (max 0 R)

theorem measurable_zeroProfileTruncation (γ : ℝ→ℝ) (hγ : Measurable γ) (R : ℝ) :
    Measurable (zeroProfileTruncation γ R) := (measurable_const.max hγ).min measurable_const

theorem zeroProfileTruncation_norm_le (γ : ℝ→ℝ) (R q : ℝ) :
    ‖zeroProfileTruncation γ R q‖≤‖γ q‖ := by
  rw [zeroProfileTruncation,Real.norm_eq_abs,Real.norm_eq_abs]
  have hn : 0≤min (max 0 (γ q)) (max 0 R) := le_min (le_max_left _ _) (le_max_left _ _)
  rw [abs_of_nonneg hn]
  exact (min_le_left _ _).trans (max_le (abs_nonneg _) (le_abs_self _))

theorem intervalIntegrable_zeroProfileTruncation (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) (R : ℝ) :
    IntervalIntegrable (zeroProfileTruncation γ R) volume (0:ℝ) 1 := by
  apply hiγ.norm.mono_fun' (measurable_zeroProfileTruncation γ hγ R).aestronglyMeasurable
  exact .of_forall fun q=>by simpa only [norm_norm] using zeroProfileTruncation_norm_le γ R q

theorem zeroProfileTruncation_difference_norm_le (γ : ℝ→ℝ) (R q : ℝ) :
    ‖zeroProfileTruncation γ R q-γ q‖≤‖γ q‖ := by
  rw [Real.norm_eq_abs,Real.norm_eq_abs]
  unfold zeroProfileTruncation
  by_cases hg : 0≤γ q
  · rw [max_eq_right hg,abs_of_nonneg hg]
    have ht : min (γ q) (max 0 R)≤γ q:=min_le_left _ _
    rw [abs_of_nonpos (by linarith)]
    have hn : 0≤min (γ q) (max 0 R):=le_min hg (le_max_left _ _)
    linarith
  · rw [max_eq_left (lt_of_not_ge hg).le,min_eq_left (le_max_left _ _)]
    simp

theorem tendsto_zeroProfileDistance_truncation (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hγ0 : ∀ᵐ q ∂volume, q∈Ioc (0:ℝ) 1→0≤γ q) :
    Tendsto (fun R:ℝ=>zeroProfileDistance (zeroProfileTruncation γ R) γ) atTop (𝓝 0) := by
  have hh : Tendsto (fun R:ℝ=>∫q in (0:ℝ)..1,‖zeroProfileTruncation γ R q-γ q‖)
      atTop (𝓝 (∫q in (0:ℝ)..1,(0:ℝ))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (bound:=fun q=>‖γ q‖)
    · exact .of_forall fun R=>((measurable_zeroProfileTruncation γ hγ R).sub hγ).norm.aestronglyMeasurable
    · exact .of_forall fun R=>.of_forall fun q _=>by
        simpa only [norm_norm] using zeroProfileTruncation_difference_norm_le γ R q
    · exact hiγ.norm
    · filter_upwards [hγ0] with q hq
      intro hqI
      rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)] at hqI
      have hg:=hq hqI
      have he : (fun R:ℝ=>‖zeroProfileTruncation γ R q-γ q‖)=ᶠ[atTop] fun _=>0 := by
        filter_upwards [eventually_ge_atTop (γ q)] with R hR
        have hR0 : 0≤R:=hg.trans hR
        simp [zeroProfileTruncation,max_eq_right hg,max_eq_right hR0,min_eq_left hR]
      exact tendsto_const_nhds.congr' he.symm
  simpa only [zeroProfileDistance,intervalIntegral.integral_zero] using hh

theorem tendstoUniformly_zeroTemperatureValue_truncation (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1)
    (hγ0 : ∀ᵐ q ∂volume,q∈Ioc (0:ℝ) 1→0≤γ q) :
    TendstoUniformly (fun R:ℝ=>zeroTemperatureValue (zeroProfileTruncation γ R))
      (zeroTemperatureValue γ) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hh:=(tendsto_zeroProfileDistance_truncation γ hγ hiγ hγ0).const_mul (3/2:ℝ)
  simp only [mul_zero] at hh
  filter_upwards [hh.eventually (gt_mem_nhds hε)] with R hR
  intro x
  rw [dist_eq_norm]
  rw [norm_sub_rev]
  exact (zeroTemperatureValue_difference_bound _ γ (measurable_zeroProfileTruncation γ hγ R)
    hγ (intervalIntegrable_zeroProfileTruncation γ hγ hiγ R) hiγ x).trans_lt hR

end QuantitativePaper
