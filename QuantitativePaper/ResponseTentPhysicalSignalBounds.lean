module
public import QuantitativePaper.ResponseTentFunctionals
public import QuantitativePaper.ResponseCurvatureLower
public import QuantitativePaper.ResponseMidpointCalculus

@[expose] public section

/-! The actual tent response signal is bounded below using the proved
physical averaged-curvature lower bound on its support. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem responseAveragedCurvature_nonneg (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) :
    0 ≤ responseAveragedCurvature (n := n) μ β t lam ht q := by
  unfold responseAveragedCurvature
  exact mul_nonneg (div_nonneg (sq_nonneg β) (Nat.cast_nonneg n))
    (integral_nonneg fun sample => (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1)

theorem responseTent_zero_of_not_mem_band (ell q : ℝ) (hell : 0 < ell)
    (hq : q ∉ Icc (ell/4) (3*ell/4)) : responseTent ell q = 0 := by
  have hn : ¬0 < responseTent ell q := by
    intro hpos
    have h := (responseTent_pos_iff hell).mp hpos
    exact hq ⟨h.1.le, h.2.le⟩
  exact le_antisymm (le_of_not_gt hn) (responseTent_bounds ell q hell).1

theorem responseTentSignal_lower (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β t lam θ ell κ U : ℝ) (hβ : 1 ≤ β) (ht : t ∈ Ico (0 : ℝ) 1)
    (hlam : 0 ≤ lam) (hell : ell ∈ Ioc (0 : ℝ) 1) (hκ : 0 ≤ κ)
    (hfloor : lam ≤ β * Paper.parisiCDF (Paper.parisiMix μ ν θ) 0)
    (hv : ∀ q ∈ Icc (ell/4) (3*ell/4), κ ≤ β * (Paper.parisiCDF ν q - Paper.parisiCDF μ q))
    (hU : ∀ q ∈ Icc (ell/4) (3*ell/4), β * Paper.parisiCDF (Paper.parisiMix μ ν θ) q ≤ U) :
    (responseCurvatureConstant U)^2 * κ * ell / 4 ≤
      responseTentSignal (n := n) μ ν β t lam θ ht.2.le ell := by
  have hpoint (q : ℝ) (hq : q ∈ Icc (0 : ℝ) 1) :
      (responseCurvatureConstant U)^2 * κ * responseTent ell q ≤
      β * (Paper.parisiCDF ν q - Paper.parisiCDF μ q) * responseTent ell q *
        responseAveragedCurvatureReal (n := n) (Paper.parisiMix μ ν θ) β t lam ht.2.le q := by
    by_cases hb : q ∈ Icc (ell/4) (3*ell/4)
    · have hz := responseAveragedCurvature_lower hn (Paper.parisiMix μ ν θ)
        β t lam U hβ ht hlam hfloor ⟨q, hq⟩ (hU q hb)
      have hw := (responseTent_bounds ell q hell.1).1
      have hvq := hv q hb
      have hv0 : 0 ≤ β * (Paper.parisiCDF ν q - Paper.parisiCDF μ q) := hκ.trans hvq
      have he : responseAveragedCurvatureReal (n := n) (Paper.parisiMix μ ν θ)
          β t lam ht.2.le q = responseAveragedCurvature (n := n) (Paper.parisiMix μ ν θ)
          β t lam ht.2.le ⟨q, hq⟩ := by
        simp only [responseAveragedCurvatureReal, projIcc_of_mem zero_le_one hq]
      rw [he]
      calc
        _ = (κ * responseTent ell q) * (responseCurvatureConstant U)^2 := by ring
        _ ≤ (β * (Paper.parisiCDF ν q - Paper.parisiCDF μ q) * responseTent ell q) *
            (responseCurvatureConstant U)^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hvq hw) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hz (mul_nonneg hv0 hw)
    · simp only [responseTent_zero_of_not_mem_band ell q hell.1 hb, mul_zero, zero_mul, le_refl]
  have h := intervalIntegral.integral_mono_on zero_le_one
    (((continuous_responseTent ell).intervalIntegrable 0 1).const_mul
      ((responseCurvatureConstant U)^2 * κ))
    (intervalIntegrable_response_tent_signal μ ν (Paper.parisiMix μ ν θ) β t lam ell 0 1 ht.2) hpoint
  rw [intervalIntegral.integral_const_mul, responseTent_interval_integral hell] at h
  change (responseCurvatureConstant U)^2 * κ * ell / 4 ≤
    ∫ q in (0 : ℝ)..1, β * (Paper.parisiCDF ν q - Paper.parisiCDF μ q) * responseTent ell q *
      responseAveragedCurvatureReal (n := n) (Paper.parisiMix μ ν θ) β t lam ht.2.le q
  convert h using 1 <;> ring

end QuantitativePaper
