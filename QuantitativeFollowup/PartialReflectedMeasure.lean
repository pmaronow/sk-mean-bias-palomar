module
public import QuantitativeFollowup.LowerReflectedDensity

@[expose] public section

/-! Actual partial reflected regularization: only free mass below T is
moved. The prescribed root and all free mass at and above T are kept. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def overlapBelow (T : ℝ) : Set Paper.Overlap:={q | (q:ℝ)<T}

theorem measurableSet_overlapBelow (T : ℝ) : MeasurableSet (overlapBelow T) :=
  measurable_subtype_coe measurableSet_Iio

def partialReflectedFreeMeasure (μ : Paper.ParisiMeasure) (s T h : ℝ) : Measure Paper.Overlap :=
  lowerReflectedMeasure ((parisiFreeMeasure μ s).restrict (overlapBelow T)) h+
    (parisiFreeMeasure μ s).restrict (overlapBelow T)ᶜ

instance partialReflectedFreeMeasure_finite (μ : Paper.ParisiMeasure) (s T h : ℝ) :
    IsFiniteMeasure (partialReflectedFreeMeasure μ s T h) := by
  unfold partialReflectedFreeMeasure;infer_instance

theorem partialReflectedFreeMeasure_univ (μ : Paper.ParisiMeasure) (s T h : ℝ) (hh : 0<h) :
    partialReflectedFreeMeasure μ s T h univ=ENNReal.ofReal (1-s) := by
  rw [partialReflectedFreeMeasure,Measure.add_apply,lowerReflectedMeasure_univ _ h hh,
    Measure.restrict_apply_univ,Measure.restrict_apply_univ,
    measure_add_measure_compl (measurableSet_overlapBelow T),parisiFreeMeasure_univ]

theorem partialReflectedFreeMeasure_root (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    partialReflectedFreeMeasure μ s T h {zeroOverlap}=0 := by
  have hη : ∀ᵐ(q:Paper.Overlap)∂(parisiFreeMeasure μ s).restrict (overlapBelow T),(q:ℝ)<T:=
    ae_restrict_mem (measurableSet_overlapBelow T)
  rw [partialReflectedFreeMeasure,Measure.add_apply,lowerReflectedMeasure_singleton _ T h hT hh hη]
  rw [zero_add,Measure.restrict_apply (measurableSet_singleton _)]
  have he : ({zeroOverlap}:Set Paper.Overlap)∩(overlapBelow T)ᶜ=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    have hq0 : q=zeroOverlap:=hq.1
    subst q
    exact hq.2 hT.1
  rw [he,measure_empty]

theorem partialReflectedFreeMeasure_density_below (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    ((partialReflectedFreeMeasure μ s T h).map (Subtype.val:Paper.Overlap→ℝ)).restrict (Iio T)≤
      (ENNReal.ofReal (1/h)*(parisiFreeMeasure μ s (overlapBelow T))) • volume.restrict (Iio T) := by
  have hη : ∀ᵐ(q:Paper.Overlap)∂(parisiFreeMeasure μ s).restrict (overlapBelow T),(q:ℝ)<T:=
    ae_restrict_mem (measurableSet_overlapBelow T)
  have hzero : (((parisiFreeMeasure μ s).restrict (overlapBelow T)ᶜ).map
      (Subtype.val:Paper.Overlap→ℝ)).restrict (Iio T)=0 := by
    apply Measure.restrict_eq_zero.mpr
    rw [Measure.map_apply measurable_subtype_coe measurableSet_Iio,
      Measure.restrict_apply (measurable_subtype_coe measurableSet_Iio)]
    change parisiFreeMeasure μ s ((overlapBelow T)∩(overlapBelow T)ᶜ)=0
    simp
  rw [partialReflectedFreeMeasure,Measure.map_add _ _ measurable_subtype_coe,
    Measure.restrict_add,hzero,add_zero]
  have hd:=Measure.restrict_mono_measure (lowerReflectedMeasure_density_le
    ((parisiFreeMeasure μ s).restrict (overlapBelow T)) T h hT hh hη) (Iio T)
  simpa only [Measure.restrict_smul,Measure.restrict_apply_univ] using hd

def partialReflectedOverlapMeasure (μ : Paper.ParisiMeasure) (s T h : ℝ) : Measure Paper.Overlap :=
  ENNReal.ofReal s • Measure.dirac zeroOverlap+partialReflectedFreeMeasure μ s T h

theorem partialReflectedOverlapMeasure_probability (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : 0<h) : IsProbabilityMeasure (partialReflectedOverlapMeasure μ s T h) := by
  constructor
  rw [partialReflectedOverlapMeasure,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one,
    partialReflectedFreeMeasure_univ μ s T h hh,←ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)]
  simp

def partialReflectedParisiMeasure (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : 0<h) : Paper.ParisiMeasure :=
  ⟨partialReflectedOverlapMeasure μ s T h,partialReflectedOverlapMeasure_probability μ s T h hs hh⟩

theorem partialReflectedParisiMeasure_root (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    zeroMass (partialReflectedParisiMeasure μ s T h hs hh.1)=s := by
  unfold zeroMass
  change ((partialReflectedOverlapMeasure μ s T h) {zeroOverlap}).toReal=s
  rw [partialReflectedOverlapMeasure,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),smul_eq_mul,mul_one,
    partialReflectedFreeMeasure_root μ s T h hT hh,add_zero,ENNReal.toReal_ofReal hs.1]

theorem partialReflectedParisiMeasure_free (μ : Paper.ParisiMeasure) (s T h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T)) :
    parisiFreeMeasure (partialReflectedParisiMeasure μ s T h hs hh.1) s=partialReflectedFreeMeasure μ s T h := by
  have hfloor : partialReflectedParisiMeasure μ s T h hs hh.1∈scalarFloor s := by
    rw [mem_scalarFloor_iff,partialReflectedParisiMeasure_root μ s T h hs hT hh]
  have hr:=root_add_parisiFreeMeasure (partialReflectedParisiMeasure μ s T h hs hh.1) s hs hfloor
  change ENNReal.ofReal s • Measure.dirac zeroOverlap+_=
    ENNReal.ofReal s • Measure.dirac zeroOverlap+_ at hr
  have : IsFiniteMeasure (ENNReal.ofReal s • Measure.dirac (zeroOverlap:Paper.Overlap)):=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  exact (Measure.add_right_inj _ _ _).mp hr

end QuantitativeFollowup
