module
public import QuantitativeFollowup.PartialReflectedRegularization
public import QuantitativeFollowup.ConcentratingMeasure

@[expose] public section

/-! The actual partial regularization's full derivative measure has the
same below-root-free density on interior localization intervals. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000

theorem parisiCDFPrimitive_free_restrict (μ : Paper.ParisiMeasure) (s : ℝ)
    (hs : s ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s)
    (I : Set ℝ) (hI : MeasurableSet I) (hzero : (0 : ℝ) ∉ I) :
    (parisiCDFPrimitive μ).measure.restrict I=
      ((parisiFreeMeasure μ s).map (Subtype.val : Paper.Overlap → ℝ)).restrict I := by
  classical
  rw [parisiCDFPrimitive_measure,←root_add_parisiFreeMeasure μ s hs hμ,
    Measure.map_add _ _ measurable_subtype_coe,
    Measure.map_smul _ measurable_subtype_coe.aemeasurable,Measure.map_dirac zeroOverlap]
  change (ENNReal.ofReal s • Measure.dirac (0 : ℝ)+(parisiFreeMeasure μ s).map Subtype.val).restrict I=_
  rw [Measure.restrict_add,Measure.restrict_smul,restrict_dirac' hI,ite_eq_right hzero,smul_zero,zero_add]

theorem partial_reflected_interior_density_le (beta : ℝ) (hbeta : 0 ≤ beta)
    (μ : Paper.ParisiMeasure) (s T h a b : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
    (hT : T ∈ Ioo (0 : ℝ) 1) (hh : h ∈ Ioc (0 : ℝ) (1-T))
    (ha : 0 < a) (hb : b ≤ T) :
    ENNReal.ofReal beta •
      (parisiCDFPrimitive (partialReflectedParisiMeasure μ s T h hs hh.1)).measure.restrict (Ioo a b) ≤
      ENNReal.ofReal (beta*(parisiFreeMeasure μ s).real (overlapBelow T)/h) • volume.restrict (Ioo a b) := by
  have hfloor : partialReflectedParisiMeasure μ s T h hs hh.1 ∈ scalarFloor s := by
    rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ s T h hs hT hh]
  rw [parisiCDFPrimitive_free_restrict _ s hs hfloor (Ioo a b) measurableSet_Ioo
    (fun hx => not_lt_of_ge ha.le hx.1)]
  have hi : Ioo a b ⊆ Iio T := fun _ hx => hx.2.trans_le hb
  have hd := Measure.restrict_mono_measure (partial_reflected_energy_density_le beta hbeta μ s T h hs hT hh) (Ioo a b)
  simpa only [Measure.restrict_smul,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr hi] using hd

end QuantitativeFollowup
