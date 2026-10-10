module
public import QuantitativeFollowup.AnisotropicRecordedProfileTree
public import QuantitativeFollowup.AnisotropicAdapted
public import FourPapersCommon.FiniteProductIndependence

@[expose] public section

/-! The complete fresh vector Wiener path is independent of the actual
anisotropic full past, including its true tilted initial disorder. This
is derived from the constructed coordinate Brownian laws, rather than
supplied as a Markov assumption. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def anisotropicRecordedFutureBrownianPath (a : ℝ≥0)
    (p : AnisotropicDisorderBrownianSample n) : VectorWienerPath n :=
  fun i=>canonicalFutureBrownianPath a (p.2 i)

theorem measurable_anisotropicRecordedFutureBrownianPath (a : ℝ≥0) :
    Measurable (anisotropicRecordedFutureBrownianPath (n:=n) a) :=
  Measurable.of_eval fun i=>(measurable_canonicalFutureBrownianPath a).comp
    ((measurable_pi_apply i).comp measurable_snd)

theorem hasLaw_anisotropicRecordedFutureBrownianPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0) :
    HasLaw (anisotropicRecordedFutureBrownianPath q) (vectorWienerMeasure n)
      (anisotropicMeasureSampleLaw D μ a) := by
  let f : VectorBrownianSample n→VectorWienerPath n:=fun w i=>canonicalFutureBrownianPath q (w i)
  have hf : Measurable f:=Measurable.of_eval fun i=>(measurable_canonicalFutureBrownianPath q).comp
    (measurable_pi_apply i)
  have hp : (vectorBrownianMeasure n).map f=vectorWienerMeasure n := by
    rw [vectorBrownianMeasure,Measure.pi_map_pi
      (fun _=>(measurable_canonicalFutureBrownianPath q).aemeasurable)]
    simp only [canonicalFutureBrownianPath_law]
    rfl
  have hh : HasLaw f (vectorWienerMeasure n) (vectorBrownianMeasure n):=⟨hf.aemeasurable,hp⟩
  exact hh.comp (hasLaw_anisotropicMeasureWienerSamples D μ a)

theorem indep_anisotropicRecordedFutureBrownianPath_past (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0) :
    IndepFun (anisotropicRecordedFutureBrownianPath q)
      (fun p : AnisotropicDisorderBrownianSample n=>fun s : Iic q=>anisotropicBrownianRecord s p)
      (anisotropicMeasureSampleLaw D μ a) := by
  let f : Fin n→Paper.BrownianSample→C(Paper.Overlap,ℝ):=fun _=>canonicalFutureBrownianPath q
  let g : Fin n→Paper.BrownianSample→(Iic q→ℝ):=fun _=>scalarBrownianPast q
  have hf : ∀i,Measurable (f i):=fun _=>measurable_canonicalFutureBrownianPath q
  have hg : ∀i,Measurable (g i):=fun _=>measurable_scalarBrownianPast q
  have hsg : Measurable[Paper.canonicalBrownianFiltration q] (scalarBrownianPast q) := by
    letI : MeasurableSpace Paper.BrownianSample:=Paper.canonicalBrownianFiltration q
    exact Measurable.of_eval fun s=>((Filtration.stronglyAdapted_natural
      (fun u=>(Paper.measurable_canonicalBrownian u).stronglyMeasurable) s).mono
        (Paper.canonicalBrownianFiltration.mono s.property)).measurable
  have hten:=indepFun_finiteProduct (fun _ : Fin n=>Paper.canonicalBrownianMeasure)
    f g hf hg (fun _=>canonicalFutureBrownianPath_indep_past q _ hsg)
  have hfg : Measurable (fun w : VectorBrownianSample n=>fun i=>f i (w i)) :=
    Measurable.of_eval fun i=>(hf i).comp (measurable_pi_apply i)
  have hgg : Measurable (fun w : VectorBrownianSample n=>fun i=>g i (w i)) :=
    Measurable.of_eval fun i=>(hg i).comp (measurable_pi_apply i)
  have hadj:=indepFun_adjoin_initial (vectorBrownianMeasure n) (anisotropicMeasureOuterLaw D μ a)
    _ _ hfg hgg hten
  let record : AnisotropicDisorder n×(Fin n→Iic q→ℝ)→(Iic q→AnisotropicObservationState n):=
    fun p s=>(p.1,WithLp.toLp 2 (fun i=>p.2 i s))
  have hr : Measurable record:=by unfold record;fun_prop
  exact hadj.comp measurable_id hr

theorem indep_anisotropicRecordedFutureBrownianPath_filtration (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0) :
    Indep (MeasurableSpace.comap (anisotropicRecordedFutureBrownianPath (n:=n) q) inferInstance)
      (anisotropicBrownianFiltration n q) (anisotropicMeasureSampleLaw D μ a) := by
  rw [anisotropicBrownianFiltration,Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp (indep_anisotropicRecordedFutureBrownianPath_past D μ a q)

theorem indep_anisotropicRecordedFutureBrownianPath_known {X : Type*} [MeasurableSpace X]
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℝ≥0) (Z : AnisotropicDisorderBrownianSample n→X)
    (hZ : Measurable[anisotropicBrownianFiltration n q] Z) :
    IndepFun (anisotropicRecordedFutureBrownianPath q) Z (anisotropicMeasureSampleLaw D μ a) :=
  (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_right (indep_anisotropicRecordedFutureBrownianPath_filtration D μ a q) hZ.comap_le)

end QuantitativeFollowup
