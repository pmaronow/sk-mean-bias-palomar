module
public import QuantitativeFollowup.ReflectedPointDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The actual lower-endpoint reflected kernel for mass strictly below
a cutoff. The radius may range up to `1−T`, as in Lemma 5.2(a). -/
noncomputable section
open Set MeasureTheory Paper
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def lowerReflectedOverlap (p : Paper.Overlap×ℝ) : Paper.Overlap :=
  projIcc (0:ℝ) 1 zero_le_one (|(p.1:ℝ)+p.2|)

theorem measurable_lowerReflectedOverlap : Measurable lowerReflectedOverlap :=
  continuous_projIcc.measurable.comp (measurable_abs.comp
    ((measurable_subtype_coe.comp measurable_fst).add measurable_snd))

theorem lowerReflectedOverlap_coe (T h : ℝ) (_hT : T∈Ioo (0:ℝ) 1)
    (hh : h∈Ioc (0:ℝ) (1-T)) (q : Paper.Overlap) (hq : (q:ℝ)<T)
    {u : ℝ} (hu : u∈Icc (-h) h) :
    (lowerReflectedOverlap (q,u):ℝ)=|(q:ℝ)+u| := by
  have habs : |(q:ℝ)+u|∈Icc (0:ℝ) 1 := by
    refine ⟨abs_nonneg _,?_⟩
    rw [abs_le]
    constructor <;>linarith [q.property.1,_hT.1,hh.2,hu.1,hu.2]
  exact congrArg Subtype.val (projIcc_of_mem _ habs)

def lowerReflectedMeasure (η : Measure Paper.Overlap) (h : ℝ) : Measure Paper.Overlap :=
  (η.prod (symmetricUniformLaw h)).map lowerReflectedOverlap

instance lowerReflectedMeasure_finite (η : Measure Paper.Overlap) [IsFiniteMeasure η] (h : ℝ) :
    IsFiniteMeasure (lowerReflectedMeasure η h) := by unfold lowerReflectedMeasure;infer_instance

theorem lowerReflectedMeasure_univ (η : Measure Paper.Overlap) [IsFiniteMeasure η]
    (h : ℝ) (hh : 0<h) : lowerReflectedMeasure η h univ=η (Set.univ:Set Paper.Overlap) := by
  have:=symmetricUniformLaw_probability h hh
  rw [lowerReflectedMeasure,Measure.map_apply measurable_lowerReflectedOverlap MeasurableSet.univ]
  simp only [preimage_univ,←Set.univ_prod_univ,Measure.prod_prod,measure_univ,mul_one]

theorem lowerReflectedMeasure_density_le (η : Measure Paper.Overlap) [IsFiniteMeasure η]
    (T h : ℝ) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T))
    (hη : ∀ᵐ(q : Paper.Overlap)∂η,(q:ℝ)<T) :
    (lowerReflectedMeasure η h).map (Subtype.val:Paper.Overlap→ℝ)≤
      (ENNReal.ofReal (1/h)*η (Set.univ:Set Paper.Overlap)) • volume := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [lowerReflectedMeasure,Measure.map_map measurable_subtype_coe measurable_lowerReflectedOverlap,
    Measure.map_apply (measurable_subtype_coe.comp measurable_lowerReflectedOverlap) hS,
    Measure.prod_apply ((measurable_subtype_coe.comp measurable_lowerReflectedOverlap) hS),Measure.smul_apply]
  have hpoint : ∀ᵐ(q : Paper.Overlap)∂η,symmetricUniformLaw h
      (Prod.mk q ⁻¹' ((Subtype.val∘lowerReflectedOverlap) ⁻¹' S))≤ENNReal.ofReal (1/h)*volume S := by
    filter_upwards [hη] with q hq
    have he : (fun u : ℝ=>(lowerReflectedOverlap (q,u):ℝ))=ᵐ[symmetricUniformLaw h]
        (fun u=>|(q:ℝ)+u|) := by
      filter_upwards [symmetricUniformLaw_ae h] with u hu
      exact lowerReflectedOverlap_coe T h hT hh q hq hu
    have hm : Measurable (fun u : ℝ=>(lowerReflectedOverlap (q,u):ℝ)):=
      measurable_subtype_coe.comp (measurable_lowerReflectedOverlap.comp (measurable_const.prodMk measurable_id))
    change symmetricUniformLaw h ((fun u : ℝ=>(lowerReflectedOverlap (q,u):ℝ)) ⁻¹' S)≤_
    rw [←Measure.map_apply hm hS,Measure.map_congr he]
    exact abs_uniform_point_density_le h hh.1 (q:ℝ) S
  calc
    _≤∫⁻ _q : Paper.Overlap,ENNReal.ofReal (1/h)*volume S ∂η:=lintegral_mono_ae hpoint
    _=_:=by rw [lintegral_const];ring

theorem lowerReflectedMeasure_singleton (η : Measure Paper.Overlap) [IsFiniteMeasure η]
    (T h : ℝ) (hT : T∈Ioo (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1-T))
    (hη : ∀ᵐ(q : Paper.Overlap)∂η,(q:ℝ)<T) (q : Paper.Overlap) : lowerReflectedMeasure η h {q}=0 := by
  have hd:=lowerReflectedMeasure_density_le η T h hT hh hη {(q:ℝ)}
  rw [Measure.smul_apply,Real.volume_singleton,smul_zero] at hd
  have he : (lowerReflectedMeasure η h).map (Subtype.val:Paper.Overlap→ℝ) {(q:ℝ)}=
      lowerReflectedMeasure η h {q} := by
    rw [Measure.map_apply measurable_subtype_coe (measurableSet_singleton _)]
    congr 1
    simpa only [Set.image_singleton] using Set.preimage_image_eq ({q}:Set Paper.Overlap) Subtype.val_injective
  exact le_zero_iff.mp (by simpa only [he] using hd)

end QuantitativeFollowup
