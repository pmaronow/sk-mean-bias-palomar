module
public import QuantitativeFollowup.ReflectedPointDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! A genuine admissible reflected profile. The prescribed root atom is
kept fixed and every unit of the actual free measure is independently
perturbed by the uniform reflected kernel. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def reflectedFreeMeasure (μ : Paper.ParisiMeasure) (s h : ℝ) : Measure Paper.Overlap :=
  ((parisiFreeMeasure μ s).prod (symmetricUniformLaw h)).map reflectedOverlap

theorem reflectedFreeMeasure_univ (μ : Paper.ParisiMeasure) (s h : ℝ) (hh : 0<h) :
    reflectedFreeMeasure μ s h univ=ENNReal.ofReal (1-s) := by
  have:=symmetricUniformLaw_probability h hh
  rw [reflectedFreeMeasure,Measure.map_apply measurable_reflectedOverlap MeasurableSet.univ]
  simp only [preimage_univ,←Set.univ_prod_univ,Measure.prod_prod,measure_univ,mul_one,parisiFreeMeasure_univ]

instance reflectedFreeMeasure_finite (μ : Paper.ParisiMeasure) (s h : ℝ) :
    IsFiniteMeasure (reflectedFreeMeasure μ s h) := by
  unfold reflectedFreeMeasure
  infer_instance

theorem reflectedFreeMeasure_density_le (μ : Paper.ParisiMeasure) (s h : ℝ)
    (_hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    (reflectedFreeMeasure μ s h).map (Subtype.val:Paper.Overlap→ℝ)≤
      ENNReal.ofReal ((1-s)/h) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [reflectedFreeMeasure,Measure.map_map measurable_subtype_coe measurable_reflectedOverlap,
    Measure.map_apply (measurable_subtype_coe.comp measurable_reflectedOverlap) hS,
    Measure.prod_apply ((measurable_subtype_coe.comp measurable_reflectedOverlap) hS),Measure.smul_apply]
  have hpoint : ∀q : Paper.Overlap,
      symmetricUniformLaw h (Prod.mk q ⁻¹' ((Subtype.val∘reflectedOverlap) ⁻¹' S))≤
        ENNReal.ofReal (1/h)*volume S := by
    intro q
    have he : (fun u : ℝ=>(reflectedOverlap (q,u):ℝ))=ᵐ[symmetricUniformLaw h]
        (fun u=>overlapReflection ((q:ℝ)+u)) := by
      filter_upwards [symmetricUniformLaw_ae h] with u hu
      exact reflectedOverlap_coe hh q hu
    have hm : Measurable (fun u : ℝ=>(reflectedOverlap (q,u):ℝ)):=
      measurable_subtype_coe.comp (measurable_reflectedOverlap.comp (measurable_const.prodMk measurable_id))
    change symmetricUniformLaw h ((fun u : ℝ=>(reflectedOverlap (q,u):ℝ)) ⁻¹' S)≤_
    rw [←Measure.map_apply hm hS,Measure.map_congr he]
    exact reflected_uniform_point_density_le h hh (q:ℝ) q.property S
  calc
    _≤∫⁻ _q : Paper.Overlap,ENNReal.ofReal (1/h)*volume S ∂parisiFreeMeasure μ s:=
      lintegral_mono hpoint
    _=ENNReal.ofReal ((1-s)/h)*volume S:=by
      rw [lintegral_const,parisiFreeMeasure_univ]
      rw [mul_right_comm,←ENNReal.ofReal_mul (by exact one_div_nonneg.mpr hh.1.le)]
      congr 1
      ring_nf

theorem reflectedFreeMeasure_singleton (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) (q : Paper.Overlap) :
    reflectedFreeMeasure μ s h {q}=0 := by
  have hd:=reflectedFreeMeasure_density_le μ s h hs hh {(q:ℝ)}
  rw [Measure.smul_apply,Real.volume_singleton,smul_zero] at hd
  have hm : (reflectedFreeMeasure μ s h).map (Subtype.val:Paper.Overlap→ℝ) {(q:ℝ)}=
      reflectedFreeMeasure μ s h {q} := by
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
    congr 1
    simpa only [Set.image_singleton] using Set.preimage_image_eq ({q}:Set Paper.Overlap) Subtype.val_injective
  exact le_zero_iff.mp (by simpa only [hm] using hd)

def reflectedOverlapMeasure (μ : Paper.ParisiMeasure) (s h : ℝ) : Measure Paper.Overlap :=
  ENNReal.ofReal s • Measure.dirac zeroOverlap+reflectedFreeMeasure μ s h

theorem reflectedOverlapMeasure_probability (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : 0<h) : IsProbabilityMeasure (reflectedOverlapMeasure μ s h) := by
  constructor
  rw [reflectedOverlapMeasure,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_univ _),smul_eq_mul,mul_one,
    reflectedFreeMeasure_univ μ s h hh,←ENNReal.ofReal_add hs.1 (sub_nonneg.mpr hs.2)]
  simp

def reflectedParisiMeasure (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : 0<h) : Paper.ParisiMeasure :=
  ⟨reflectedOverlapMeasure μ s h,reflectedOverlapMeasure_probability μ s h hs hh⟩

theorem reflectedParisiMeasure_root (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    zeroMass (reflectedParisiMeasure μ s h hs hh.1)=s := by
  unfold zeroMass
  change ((reflectedOverlapMeasure μ s h) {zeroOverlap}).toReal=s
  rw [reflectedOverlapMeasure,Measure.add_apply,Measure.smul_apply,
    Measure.dirac_apply_of_mem (mem_singleton _),smul_eq_mul,mul_one,
    reflectedFreeMeasure_singleton μ s h hs hh,add_zero,ENNReal.toReal_ofReal hs.1]

theorem reflectedParisiMeasure_mem_floor (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    reflectedParisiMeasure μ s h hs hh.1∈scalarFloor s := by
  rw [mem_scalarFloor_iff,reflectedParisiMeasure_root μ s h hs hh]

theorem reflectedParisiMeasure_free (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    parisiFreeMeasure (reflectedParisiMeasure μ s h hs hh.1) s=reflectedFreeMeasure μ s h := by
  have hr:=root_add_parisiFreeMeasure (reflectedParisiMeasure μ s h hs hh.1) s hs
    (reflectedParisiMeasure_mem_floor μ s h hs hh)
  change ENNReal.ofReal s • Measure.dirac zeroOverlap+_=
    ENNReal.ofReal s • Measure.dirac zeroOverlap+_ at hr
  have : IsFiniteMeasure (ENNReal.ofReal s • Measure.dirac (zeroOverlap:Paper.Overlap)):=Measure.smul_finite _ ENNReal.ofReal_ne_top
  exact (Measure.add_right_inj _ _ _).mp hr

end QuantitativeFollowup
