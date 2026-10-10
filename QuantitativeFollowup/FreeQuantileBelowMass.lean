module
public import QuantitativeFollowup.ParisiFreeQuantile
public import QuantitativeFollowup.PartialReflectedMeasure

@[expose] public section

/-! Mass strictly below a free quantile, retaining every possible atom
at the quantile and the prescribed root normalization. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem parisiFreeQuantile_below_mass_monotone (μ : Paper.ParisiMeasure) (s : ℝ) :
    Monotone (parisiFreeQuantile μ s) := by
  intro v w hvw
  exact parisiQuantile_monotone μ (add_le_add (le_refl s) hvw)

theorem parisiFreeMeasure_below_quantile_le (μ : Paper.ParisiMeasure) (s v q : ℝ)
    (hv : 0 < v) (hq : q ≤ (parisiFreeQuantile μ s v : ℝ)) :
    (parisiFreeMeasure μ s).real (overlapBelow q) ≤ v := by
  have hm : parisiFreeMeasure μ s (overlapBelow q)=
      volume ((parisiFreeQuantile μ s) ⁻¹' overlapBelow q∩Ioc (0 : ℝ) (1-s)) := by
    rw [←parisiFreeQuantile_map μ s,Measure.map_apply (parisiFreeQuantile_measurable μ s)
      (measurableSet_overlapBelow q),Measure.restrict_apply ((parisiFreeQuantile_measurable μ s) (measurableSet_overlapBelow q))]
  have hsub : (parisiFreeQuantile μ s) ⁻¹' overlapBelow q∩Ioc (0 : ℝ) (1-s) ⊆ Ioo (0 : ℝ) v := by
    intro w hw
    refine ⟨hw.2.1,?_⟩
    by_contra hn
    have hmono := parisiFreeQuantile_below_mass_monotone μ s (le_of_not_gt hn)
    exact not_lt_of_ge (hq.trans hmono) hw.1
  have hbound := measure_mono (μ:=volume) hsub
  rw [←hm,Real.volume_Ioo,sub_zero] at hbound
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [Measure.real,ENNReal.toReal_ofReal hv.le] using hh

theorem parisiFreeMeasure_energy_below_quantile_le (μ : Paper.ParisiMeasure)
    (beta lam v q : ℝ) (hbeta : 0 < beta) (hv : 0 < v)
    (hq : q ≤ (parisiFreeQuantile μ (lam/beta) (v/beta) : ℝ)) :
    beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow q) ≤ v := by
  have hh := mul_le_mul_of_nonneg_left
    (parisiFreeMeasure_below_quantile_le μ (lam/beta) (v/beta) q (div_pos hv hbeta) hq) hbeta.le
  have he : beta*(v/beta)=v := by field_simp
  rwa [he] at hh

end QuantitativeFollowup
