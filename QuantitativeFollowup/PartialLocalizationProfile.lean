module
public import QuantitativeFollowup.PartialFunctionalRegularization
public import QuantitativeFollowup.ConcentratingMeasure

@[expose] public section

/-! The literal below-cutoff profile bound for the actual partial reflected
regularization. The possible atom at the cutoff remains outside its mass. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem partialReflectedParisiMeasure_cdf_below (μ : Paper.ParisiMeasure)
    (s T h : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hh : 0 < h)
    (x : ℝ) (hx : x ∈ Ico (0 : ℝ) T) :
    s ≤ parisiCDF (partialReflectedParisiMeasure μ s T h hs hh) x ∧
      parisiCDF (partialReflectedParisiMeasure μ s T h hs hh) x ≤
        s+(parisiFreeMeasure μ s).real (overlapBelow T) := by
  let E : Set Paper.Overlap := {r | (r : ℝ) ≤ x}
  have hE : MeasurableSet E := measurable_subtype_coe measurableSet_Iic
  have h0E : zeroOverlap ∈ E := hx.1
  have htail : ((parisiFreeMeasure μ s).restrict (overlapBelow T)ᶜ) E=0 := by
    rw [Measure.restrict_apply hE]
    have he : E∩(overlapBelow T)ᶜ=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro r hr
      exact hr.2 (lt_of_le_of_lt hr.1 hx.2)
    rw [he,measure_empty]
  have hvalue : parisiCDF (partialReflectedParisiMeasure μ s T h hs hh) x=
      s+(lowerReflectedMeasure ((parisiFreeMeasure μ s).restrict (overlapBelow T)) h E).toReal := by
    unfold parisiCDF
    change (partialReflectedOverlapMeasure μ s T h E).toReal=_
    rw [partialReflectedOverlapMeasure,Measure.add_apply,Measure.smul_apply,
      Measure.dirac_apply_of_mem h0E,smul_eq_mul,mul_one,partialReflectedFreeMeasure,
      Measure.add_apply,htail,add_zero,
      ENNReal.toReal_add ENNReal.ofReal_ne_top (measure_ne_top _ E),ENNReal.toReal_ofReal hs.1]
  rw [hvalue]
  constructor
  · exact le_add_of_nonneg_right ENNReal.toReal_nonneg
  · have hm := measure_mono (show E ⊆ univ from subset_univ _)
      (μ:=lowerReflectedMeasure ((parisiFreeMeasure μ s).restrict (overlapBelow T)) h)
    rw [lowerReflectedMeasure_univ _ h hh,Measure.restrict_apply_univ] at hm
    have hr := ENNReal.toReal_mono (measure_ne_top (parisiFreeMeasure μ s) (overlapBelow T)) hm
    exact add_le_add (le_refl s) hr

theorem partial_reflected_energy_profile_below (beta lam T h : ℝ)
    (hbeta : 0 < beta) (hlam : lam ∈ Icc (0 : ℝ) beta) (μ : Paper.ParisiMeasure)
    (hh : 0 < h) (x : ℝ) (hx : x ∈ Ico (0 : ℝ) T) :
    beta*parisiCDF (partialReflectedParisiMeasure μ (lam/beta) T h
      ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ hh) x ≤
      lam+beta*(parisiFreeMeasure μ (lam/beta)).real (overlapBelow T) := by
  have hp := mul_le_mul_of_nonneg_left (partialReflectedParisiMeasure_cdf_below μ (lam/beta) T h
    ⟨div_nonneg hlam.1 hbeta.le,(div_le_one hbeta).mpr hlam.2⟩ hh x hx).2 hbeta.le
  have hid : beta*(lam/beta)=lam := by field_simp
  rw [mul_add,hid] at hp
  exact hp

end QuantitativeFollowup
