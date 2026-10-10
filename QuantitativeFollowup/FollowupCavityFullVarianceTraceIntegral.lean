module
public import QuantitativeFollowup.FollowupCavityFullVarianceTraceSite

@[expose] public section

/-! Exact integration of the physical u=1 one-site variance decomposition.
This is the endpoint half of the final trace identity; Taylor and the true
zero-response identity are consumed separately. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followupCavityCpp_one_eq_variance_difference (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (q : Paper.Overlap) :
    followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one, le_rfl⟩ q =
      ((n+1 : ℕ) : ℝ)/(n : ℝ) *
        variance (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) (by linarith [hρ.1]) q)
          (vectorMeasureDisorderTilt μ β (1-ρ) a) -
      (n : ℝ)⁻¹ * variance (vectorMeasureSiteSquare μ β (1-ρ) (by linarith [hρ.1]) q (Fin.last n))
        (vectorMeasureDisorderTilt μ β (1-ρ) a) := by
  have h := followup_full_variance_trace_endpoint hn μ β ρ a hβ hρ q
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hN0 : ((n+1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hn0, hN0] at h ⊢
  nlinarith

theorem integrable_followupCavityCpp_one (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    Integrable (fun q => followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one, le_rfl⟩ q)
      (parisiFreeMeasure μ a) := by
  have hi0 := integrable_variance_vectorSelfOverlap (by omega : 0 < n+1) μ β (1-ρ) a
    (by linarith [hρ.1]) (parisiFreeMeasure μ a)
  have hiV : Integrable (fun q : Paper.Overlap =>
      variance (vectorMeasureSelfSquare (n:=n+1) μ β (1-ρ) (by linarith [hρ.1]) q)
        (vectorMeasureDisorderTilt μ β (1-ρ) a)) (parisiFreeMeasure μ a) :=
    hi0.congr (.of_forall fun q => (variance_vectorMeasureSelfSquare_eq_marked μ β (1-ρ) a _ q).symm)
  have hiS := integrable_vectorMeasureSiteVariance μ β (1-ρ) a (by linarith [hρ.1])
    (Fin.last n) (parisiFreeMeasure μ a)
  exact ((hiV.const_mul (((n+1 : ℕ) : ℝ)/(n : ℝ))).sub (hiS.const_mul (n : ℝ)⁻¹)).congr
    (.of_forall fun q => (followupCavityCpp_one_eq_variance_difference hn μ β ρ a hβ hρ q).symm)

theorem followup_full_variance_trace_endpoint_integral (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β ρ a : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    vectorIntegratedSelfOverlapVariance (n:=n+1) μ a β (1-ρ) (by linarith [hρ.1]) =
      followupCavitySiteVariance n β ρ hρ μ a / ((n+1 : ℕ) : ℝ) +
      (n : ℝ)/((n+1 : ℕ) : ℝ) *
        (∫q, followupCavityCpp n β ρ hβ hρ μ a 1 ⟨zero_le_one, le_rfl⟩ q ∂parisiFreeMeasure μ a) := by
  rw [vectorIntegratedSelfOverlapVariance_eq_free_integral (by omega : 0 < n+1)]
  simp_rw [← variance_vectorMeasureSelfSquare_eq_marked μ β (1-ρ) a]
  have hiS := integrable_vectorMeasureSiteVariance μ β (1-ρ) a (by linarith [hρ.1])
    (Fin.last n) (parisiFreeMeasure μ a)
  have hiC := integrable_followupCavityCpp_one hn μ β ρ a hβ hρ
  have he := integral_congr_ae (μ:=parisiFreeMeasure μ a)
    (.of_forall fun q => followup_full_variance_trace_endpoint hn μ β ρ a hβ hρ q)
  rw [he]
  rw [integral_add (hiS.div_const _) (hiC.const_mul _), integral_div, integral_const_mul]
  rfl

end QuantitativeFollowup
