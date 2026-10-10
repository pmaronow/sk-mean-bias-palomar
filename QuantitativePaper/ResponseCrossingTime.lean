module
public import QuantitativePaper.ResponseModel
public import QuantitativeFollowup.ParisiQuantile

@[expose] public section

/-! A genuine CDF crossing time supplies the finite-prefix curvature stage.
The threshold is attained at atoms by right continuity of the actual CDF. -/
noncomputable section
open Set Paper
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 1000000

theorem exists_responseCrossingTime (μ : ParisiMeasure) (β a U : ℝ)
    (hβ : 1 ≤ β) (ha : a ≤ parisiCDF μ 0) (q : Overlap)
    (hU : β*parisiCDF μ q ≤ U) :
    ∃T : Overlap,q ≤ T ∧ 1 ≤ β*parisiCDF μ T ∧
      (∀r : ℝ,r ∈ Icc 0 1 → r < T → β*parisiCDF μ r ≤ max 1 U) ∧
      β*a ≤ max 1 U := by
  have hβp : 0 < β := lt_of_lt_of_le (by norm_num) hβ
  have haU : β*a ≤ max 1 U :=
    (mul_le_mul_of_nonneg_left (ha.trans (parisiCDF_monotone μ q.property.1)) hβp.le).trans
      (hU.trans (le_max_right _ _))
  by_cases hq : 1 ≤ β*parisiCDF μ q
  · refine ⟨q,le_rfl,hq,?_,haU⟩
    intro r _ hr
    exact (mul_le_mul_of_nonneg_left (parisiCDF_monotone μ hr.le) hβp.le).trans
      (hU.trans (le_max_right _ _))
  · have hv : (1/β) ∈ Icc (0 : ℝ) 1 :=
      ⟨by positivity,(div_le_one hβp).mpr hβ⟩
    let T : Overlap := ⟨parisiQuantile μ (1/β),parisiQuantile_mem μ (1/β)⟩
    have hTc : 1/β ≤ parisiCDF μ T := le_parisiCDF_quantile μ hv
    have hQT : q ≤ T := by
      by_contra h
      have hh := hTc.trans (parisiCDF_monotone μ (le_of_lt (lt_of_not_ge h)))
      have hmul := mul_le_mul_of_nonneg_left hh hβp.le
      have hc : β*(1/β)=1 := by field_simp
      rw [hc] at hmul
      exact hq hmul
    refine ⟨T,hQT,?_,?_,haU⟩
    · have hh := mul_le_mul_of_nonneg_left hTc hβp.le
      simpa only [mul_one_div_cancel hβp.ne'] using hh
    · intro r hr hrT
      have hn : ¬1/β ≤ parisiCDF μ r := by
        intro hc
        have hh := (parisiQuantile_le_iff μ (1/β) r hr).mpr
          (by simpa only [quantileLevel_eq hv] using hc)
        exact (not_le_of_gt hrT) hh
      have hmul := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hn)) hβp.le
      have hc : β*(1/β)=1 := by field_simp
      rw [hc] at hmul
      exact hmul.trans (le_max_left _ _)

end QuantitativePaper
