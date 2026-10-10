module
public import QuantitativeFollowup.ReflectedMeasure
public import FourPapersCommon.CouplingCDFL1

@[expose] public section

/-! The true coupling of the original and reflected overlap profiles.
Its prescribed root remains fixed; its other points move by at most h. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper
open scoped ENNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def reflectedCoupling (μ : Paper.ParisiMeasure) (s h : ℝ) : Measure (Paper.Overlap×Paper.Overlap) :=
  ENNReal.ofReal s • Measure.dirac (zeroOverlap,zeroOverlap)+
    ((parisiFreeMeasure μ s).prod (symmetricUniformLaw h)).map
      (fun p=>(p.1,reflectedOverlap p))

theorem reflectedCoupling_first (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hh : 0<h) :
    (reflectedCoupling μ s h).map Prod.fst=(μ:Measure Paper.Overlap) := by
  have:=symmetricUniformLaw_probability h hh
  rw [reflectedCoupling,Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable,Measure.map_dirac,
    Measure.map_map measurable_fst (measurable_fst.prodMk measurable_reflectedOverlap)]
  change ENNReal.ofReal s • Measure.dirac zeroOverlap+
    ((parisiFreeMeasure μ s).prod (symmetricUniformLaw h)).map Prod.fst=_
  rw [Measure.map_fst_prod,measure_univ,one_smul]
  exact root_add_parisiFreeMeasure μ s hs hμ

theorem reflectedCoupling_second (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : 0<h) :
    (reflectedCoupling μ s h).map Prod.snd=
      (reflectedParisiMeasure μ s h hs hh:Measure Paper.Overlap) := by
  rw [reflectedCoupling,Measure.map_add _ _ measurable_snd,
    Measure.map_smul _ measurable_snd.aemeasurable,Measure.map_dirac,
    Measure.map_map measurable_snd (measurable_fst.prodMk measurable_reflectedOverlap)]
  rfl

theorem reflectedCoupling_probability (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hh : 0<h) :
    IsProbabilityMeasure (reflectedCoupling μ s h) := by
  apply (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mp
  rw [reflectedCoupling_first μ s h hs hμ hh]
  infer_instance

theorem reflectedCoupling_mean_displacement_le (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hh : h∈Ioc (0:ℝ) (1/2)) :
    (∫p,|(p.1:ℝ)-(p.2:ℝ)|∂reflectedCoupling μ s h)≤(1-s)*h := by
  have:=symmetricUniformLaw_probability h hh.1
  let Q := (parisiFreeMeasure μ s).prod (symmetricUniformLaw h)
  let f : Paper.Overlap×Paper.Overlap→ℝ:=fun p=>|(p.1:ℝ)-(p.2:ℝ)|
  have hf : Continuous f:=((continuous_subtype_val.comp continuous_fst).sub
    (continuous_subtype_val.comp continuous_snd)).abs
  have hi (P : Measure (Paper.Overlap×Paper.Overlap)) [IsFiniteMeasure P] : Integrable f P:=by
    simpa only [IntegrableOn,Measure.restrict_univ] using hf.continuousOn.integrableOn_compact
      (μ:=P) isCompact_univ
  have hroot : IsFiniteMeasure (ENNReal.ofReal s • Measure.dirac (zeroOverlap,zeroOverlap)):=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  change (∫p,f p∂reflectedCoupling μ s h)≤_
  rw [reflectedCoupling,integral_add_measure (hi _) (hi _),integral_smul_measure,
    integral_dirac,show f (zeroOverlap,zeroOverlap)=0 by simp [f],smul_zero,zero_add,
    integral_map (measurable_fst.prodMk measurable_reflectedOverlap).aemeasurable hf.aestronglyMeasurable]
  have him : Integrable (fun p : Paper.Overlap×ℝ=>f (p.1,reflectedOverlap p)) Q:=
    (integrable_map_measure hf.aestronglyMeasurable
      (measurable_fst.prodMk measurable_reflectedOverlap).aemeasurable).mp (hi _)
  have ha : ∀ᵐp∂Q,p.2∈Icc (-h) h:=Measure.quasiMeasurePreserving_snd.ae (symmetricUniformLaw_ae h)
  calc
    _≤∫_p,h∂Q:=by
      apply integral_mono_ae him (integrable_const h)
      filter_upwards [ha] with p hp
      dsimp only [f]
      rw [abs_sub_comm]
      exact reflectedOverlap_displacement hh p.1 hp
    _=(1-s)*h:=by
      rw [integral_const,Measure.real,←Set.univ_prod_univ,Measure.prod_prod,
        parisiFreeMeasure_univ,measure_univ,mul_one,ENNReal.toReal_ofReal (sub_nonneg.mpr hs.2)]
      rfl

theorem reflectedParisiMeasure_cdfDistance_le (μ : Paper.ParisiMeasure) (s h : ℝ)
    (hs : s∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor s) (hh : h∈Ioc (0:ℝ) (1/2)) :
    parisiCDFDistance μ (reflectedParisiMeasure μ s h hs hh.1)≤(1-s)*h := by
  have:=reflectedCoupling_probability μ s h hs hμ hh.1
  exact (FourPapersCommon.parisiCDFDistance_le_coupling _ _ (reflectedCoupling μ s h)
    (reflectedCoupling_first μ s h hs hμ hh.1) (reflectedCoupling_second μ s h hs hh.1)).trans
      (reflectedCoupling_mean_displacement_le μ s h hs hh)

end QuantitativeFollowup
