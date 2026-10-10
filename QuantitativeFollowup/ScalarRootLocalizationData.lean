module
public import QuantitativeFollowup.ScalarRootDensityMeasure
public import QuantitativeFollowup.ClippedTrialLocalDensity

@[expose] public section

/-! Genuine beta-only scalar root data for the concentrating localization
argument, including its source normalizations and ordinary measure bounds. -/
noncomputable section
open Set MeasureTheory Paper FRSB
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem scalar_root_localization_data (beta : ℝ) (hbeta : 1 < beta) :
    ∃q k C T₀ T₁ : ℝ,
      q ∈ Ioo (0 : ℝ) 1 ∧ parisiSupport (parisiMinimizer beta 0)=Icc (0 : ℝ) q ∧
      0 < k ∧ 1 ≤ C ∧ k ≤ C ∧ T₀ ∈ Ioo (0 : ℝ) q ∧ T₀ ≤ 1/4 ∧ C*T₀ ≤ 2 ∧
      T₁ ∈ Ioc (0 : ℝ) T₀ ∧
      (∀r∈Icc (0 : ℝ) T₀, k*r ≤ beta*parisiCDF (parisiMinimizer beta 0) r) ∧
      (ENNReal.ofReal (k/2) • volume.restrict (Icc (0 : ℝ) T₁) ≤
        ENNReal.ofReal beta • (parisiCDFPrimitive (parisiMinimizer beta 0)).measure.restrict (Icc (0 : ℝ) T₁)) ∧
      (∀lam : ℝ, (scalarTrialStieltjes beta (zero_le_one.trans hbeta.le) lam (parisiMinimizer beta 0)).measure.restrict (Iio q) ≤
        ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) q)) := by
  have hb : 0 < beta := zero_lt_one.trans hbeta
  obtain ⟨q,hq,hsupp⟩ := minimizer_full_support beta hbeta _ (isParisiMinimizer_selected beta 0)
  obtain ⟨k,T,hk,hT,hgrowth⟩ := scalar_minimizer_cdf_linear_lower beta hb _
    (isParisiMinimizer_selected beta 0) q hq hsupp
  obtain ⟨L,hL,hupper⟩ := scalar_trial_density_domination beta hb _
    (isParisiMinimizer_selected beta 0) q hq hsupp
  let C := max L k
  have hC : 1 ≤ C := hL.trans (le_max_left _ _)
  have hCp : 0 < C := zero_lt_one.trans_le hC
  let T₀ := min T (min (1/4) (2/C))
  have hT₀p : 0 < T₀ := lt_min hT.1 (lt_min (by norm_num) (div_pos (by norm_num) hCp))
  have hT₀T : T₀ ≤ T := min_le_left _ _
  have hT₀q : T₀ < q := hT₀T.trans_lt hT.2
  have hG : ∀r∈Icc (0 : ℝ) T₀, k*r ≤ beta*parisiCDF (parisiMinimizer beta 0) r :=
    fun r hr => hgrowth r ⟨hr.1,hr.2.trans hT₀T⟩
  obtain ⟨T₁,hT₁,hlower⟩ := scalar_root_density_measure_lower_of_linear_growth beta hb _
    (isParisiMinimizer_selected beta 0) q hq hsupp k T₀ hk ⟨hT₀p,hT₀q⟩ hG
  rw [scalar_zero_floor_free_measure_eq beta hb.le,Measure.restrict_smul,
    ←parisiCDFPrimitive_measure] at hlower
  refine ⟨q,k,C,T₀,T₁,hq,hsupp,hk,hC,le_max_right _ _,⟨hT₀p,hT₀q⟩,
    (min_le_right _ _).trans (min_le_left _ _),?_,hT₁,hG,hlower,?_⟩
  · have hh : T₀ ≤ 2/C := (min_le_right _ _).trans (min_le_right _ _)
    have hm := (le_div_iff₀ hCp).mp hh
    nlinarith
  · intro lam
    apply (hupper lam).trans
    intro S
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_left L k)) (by positivity)

end QuantitativeFollowup
