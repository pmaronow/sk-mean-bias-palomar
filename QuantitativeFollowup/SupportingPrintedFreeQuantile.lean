module
public import QuantitativeFollowup.ParisiFreeQuantile

@[expose] public section

/-! The displayed infimum is the generalized inverse of the actual free
measure, including its remaining root atom. Open versus half-open level
intervals agree under Lebesgue measure. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 700000

theorem parisiFreeMeasure_real_cdf (μ : Paper.ParisiMeasure) (s x : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hx : x ∈ Icc (0 : ℝ) 1) :
    (parisiFreeMeasure μ s).real {q : Paper.Overlap | (q : ℝ) ≤ x} = parisiCDF μ x-s := by
  rw [Measure.real, parisiFreeMeasure_cdf μ s x hs hμ hx, ENNReal.toReal_ofReal]
  linarith [scalarFloor_cdf_lower hμ hx.1]

theorem parisiFreeQuantile_printed_inf (μ : Paper.ParisiMeasure) (s v : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (hv : v ∈ Ioo (0 : ℝ) (1-s)) :
    (parisiFreeQuantile μ s v : ℝ) =
      sInf {q : ℝ | q ∈ Icc (0 : ℝ) 1 ∧
        v ≤ (parisiFreeMeasure μ s).real {r : Paper.Overlap | (r : ℝ) ≤ q}} := by
  have hlevel : s+v ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hs.1,hv.1],by linarith [hv.2]⟩
  have he : {q : ℝ | q ∈ Icc (0 : ℝ) 1 ∧
      v ≤ (parisiFreeMeasure μ s).real {r : Paper.Overlap | (r : ℝ) ≤ q}} =
      parisiQuantileSet μ (s+v) := by
    ext q
    simp only [mem_setOf_eq, parisiQuantileSet]
    constructor
    · rintro ⟨hq,hv'⟩
      rw [parisiFreeMeasure_real_cdf μ s q hs hμ hq] at hv'
      exact ⟨hq,by rw [quantileLevel_eq hlevel];linarith⟩
    · rintro ⟨hq,hv'⟩
      rw [quantileLevel_eq hlevel] at hv'
      exact ⟨hq,by rw [parisiFreeMeasure_real_cdf μ s q hs hμ hq];linarith⟩
  rw [he]
  rfl

theorem parisiFreeQuantile_printed_open_map (μ : Paper.ParisiMeasure) (s : ℝ) :
    (volume.restrict (Ioo (0 : ℝ) (1-s))).map (parisiFreeQuantile μ s) =
      parisiFreeMeasure μ s := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact parisiFreeQuantile_map μ s

theorem parisiFreeQuantile_printed_cumulative (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) {v : ℝ} (hv : v ∈ Ioo (0 : ℝ) (1-s)) :
    s+v ≤ parisiCDF μ (parisiFreeQuantile μ s v) :=
  parisiCDF_freeQuantile_lower μ s hs ⟨hv.1,hv.2.le⟩

end QuantitativeFollowup
