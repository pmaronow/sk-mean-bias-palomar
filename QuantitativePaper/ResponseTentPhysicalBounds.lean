module
public import QuantitativePaper.ResponseTentPhysicalSignalBounds

@[expose] public section

/-! The literal physical tent energy denominator is controlled by its
time mean-response bound and its closed-band Stieltjes curvature budget. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem responseTentSlope_interval_energy (ell : ℝ) (hell : ell ∈ Ioc (0 : ℝ) 1) :
    (∫ q in (0 : ℝ)..1, (responseTentSlope ell q)^2) = 8 / ell := by
  calc
    _ = ∫ q in (0 : ℝ)..1, |deriv (responseTent ell) q|^2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_deriv_responseTent hell.1] with q hq
      intro _
      rw [hq, sq_abs]
    _ = _ := responseTent_deriv_interval_energy hell

theorem responseTentEnergyDenominator_upper (μ ν : Paper.ParisiMeasure)
    (β t lam θ ell bbar sigmaBudget : ℝ) (hβ : 0 ≤ β) (ht : t < 1)
    (hell : ell ∈ Ioc (0 : ℝ) 1)
    (hb : ∀ q ∈ Icc (ell/4) (3*ell/4),
      responseMeanHessianReal (n := n) (Paper.parisiMix μ ν θ) β t lam ht.le q ≤ bbar)
    (hSigma : (1-t) * β * (∫ q : Paper.Overlap in
      {q | (q : ℝ) ∈ Icc (ell/4) (3*ell/4)},
      responseAveragedCurvature (n := n) (Paper.parisiMix μ ν θ) β t lam ht.le q
        ∂(Paper.parisiMix μ ν θ : Measure Paper.Overlap)) ≤ sigmaBudget) :
    responseTentEnergyDenominator (n := n) μ ν β t lam θ ht.le ell ≤
      8 * bbar / ell + 2 * sigmaBudget := by
  let ρ := Paper.parisiMix μ ν θ
  let S : Set Paper.Overlap := {q | (q : ℝ) ∈ Icc (ell/4) (3*ell/4)}
  have hS : MeasurableSet S := measurable_subtype_coe measurableSet_Icc
  have hsInt : IntervalIntegrable (fun q : ℝ => (responseTentSlope ell q)^2) volume 0 1 := by
    simpa only [mul_one] using intervalIntegrable_responseTentSlope_sq_mul ell 0 1
      (fun _ => (1 : ℝ)) intervalIntegrable_const
  have hmean := intervalIntegral.integral_mono_on zero_le_one
    (intervalIntegrable_response_tent_mean (n := n) ρ β t lam ell 0 1 ht.le)
    (hsInt.const_mul bbar) (fun q _ => by
      by_cases hq : q ∈ Icc (ell/4) (3*ell/4)
      · simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hb q hq)
          (sq_nonneg (responseTentSlope ell q))
      · have hn : q ∉ Ico (ell/4) (3*ell/4) := fun h => hq ⟨h.1, h.2.le⟩
        rw [congrFun (responseTentSlope_sq hell.1) q, indicator_of_notMem hn]
        simp)
  rw [intervalIntegral.integral_const_mul, responseTentSlope_interval_energy ell hell] at hmean
  have hc := continuous_responseAveragedCurvature (n := n) ρ β t lam ht
  have hi : Integrable (fun q : Paper.Overlap => (responseTent ell q)^2 *
      responseAveragedCurvature (n := n) ρ β t lam ht.le q) (ρ : Measure Paper.Overlap) :=
    ((((continuous_responseTent ell).comp continuous_subtype_val).pow 2).mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hz : Integrable (responseAveragedCurvature (n := n) ρ β t lam ht.le)
      (ρ : Measure Paper.Overlap) := hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcurv := integral_mono hi (hz.indicator hS) (fun q => by
    by_cases hq : q ∈ S
    · rw [indicator_of_mem hq]
      have hw := responseTent_bounds ell (q : ℝ) hell.1
      have hw2 : (responseTent ell q)^2 ≤ 1 := by nlinarith [sq_nonneg (responseTent ell q)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hw2
        (responseAveragedCurvature_nonneg ρ β t lam ht.le q)
    · rw [indicator_of_notMem hq,
        responseTent_zero_of_not_mem_band ell (q : ℝ) hell.1 hq]
      simp)
  rw [integral_indicator hS] at hcurv
  have hcoef : 0 ≤ (1-t) * β := mul_nonneg (sub_pos.mpr ht).le hβ
  have hbudget := (mul_le_mul_of_nonneg_left hcurv hcoef).trans hSigma
  change (∫ q in (0 : ℝ)..1, (responseTentSlope ell q)^2 *
      responseMeanHessianReal (n := n) ρ β t lam ht.le q) +
      2 * (1-t) * β * (∫ q : Paper.Overlap, (responseTent ell q)^2 *
        responseAveragedCurvature (n := n) ρ β t lam ht.le q ∂(ρ : Measure Paper.Overlap)) ≤ _
  convert add_le_add hmean (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 2))
    using 1 <;> ring

end QuantitativePaper
