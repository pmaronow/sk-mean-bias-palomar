module
public import QuantitativeFollowup.AnisotropicSpinSecondSquareKernel
public import QuantitativePaper.VectorBrownianFuture

@[expose] public section

/-! The whole future coordinate Wiener path keeps its genuine independent
law under the actual initial anisotropic disorder tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper
open scoped NNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def anisotropicFutureBrownianPath (q : ℝ≥0)
    (sample : AnisotropicDisorderBrownianSample n) : VectorWienerPath n :=
  fun i=>canonicalFutureBrownianPath q (sample.2 i)

theorem measurable_anisotropicFutureBrownianPath (q : ℝ≥0) :
    Measurable (anisotropicFutureBrownianPath (n:=n) q) :=
  Measurable.of_eval fun i=>(measurable_canonicalFutureBrownianPath q).comp
    ((measurable_pi_apply i).comp measurable_snd)

theorem hasLaw_anisotropicFutureBrownianPath (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0) :
    HasLaw (anisotropicFutureBrownianPath (n:=n) q) (vectorWienerMeasure n)
      (anisotropicMeasureSampleLaw D μ a) := by
  let f : VectorBrownianSample n→VectorWienerPath n :=
    fun w i=>canonicalFutureBrownianPath q (w i)
  have hf : Measurable f := Measurable.of_eval fun i=>
    (measurable_canonicalFutureBrownianPath q).comp (measurable_pi_apply i)
  have hp : (vectorBrownianMeasure n).map f=vectorWienerMeasure n := by
    rw [vectorBrownianMeasure,Measure.pi_map_pi
      (fun _=>(measurable_canonicalFutureBrownianPath q).aemeasurable)]
    simp only [canonicalFutureBrownianPath_law]
    rfl
  have hh : HasLaw f (vectorWienerMeasure n) (vectorBrownianMeasure n) := ⟨hf.aemeasurable,hp⟩
  exact hh.comp (show HasLaw (Prod.snd : AnisotropicDisorderBrownianSample n→VectorBrownianSample n)
    (vectorBrownianMeasure n) (anisotropicMeasureSampleLaw D μ a) from
      ⟨measurable_snd.aemeasurable,by
        simp only [anisotropicMeasureSampleLaw,Measure.map_snd_prod,measure_univ,one_smul]⟩)

theorem indep_anisotropicFutureBrownianPath_filtration (D : AnisotropicSpinModel n)
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ≥0) :
    Indep (MeasurableSpace.comap (anisotropicFutureBrownianPath (n:=n) q) inferInstance)
      (anisotropicBrownianFiltration n q) (anisotropicMeasureSampleLaw D μ a) := by
  let f : Fin n→Paper.BrownianSample→C(Paper.Overlap,ℝ) := fun _=>canonicalFutureBrownianPath q
  let g : Fin n→Paper.BrownianSample→(Iic q→ℝ) := fun _=>scalarBrownianPast q
  have hf : ∀i,Measurable (f i) := fun _=>measurable_canonicalFutureBrownianPath q
  have hg : ∀i,Measurable (g i) := fun _=>measurable_scalarBrownianPast q
  have hsg : Measurable[Paper.canonicalBrownianFiltration q] (scalarBrownianPast q) := by
    letI : MeasurableSpace Paper.BrownianSample:=Paper.canonicalBrownianFiltration q
    exact Measurable.of_eval fun s=>((Filtration.stronglyAdapted_natural
      (fun u=>(Paper.measurable_canonicalBrownian u).stronglyMeasurable) s).mono
        (Paper.canonicalBrownianFiltration.mono s.property)).measurable
  have hten:=indepFun_finiteProduct (fun _:Fin n=>Paper.canonicalBrownianMeasure)
    f g hf hg (fun _=>canonicalFutureBrownianPath_indep_past q _ hsg)
  have hfg : Measurable (fun w : VectorBrownianSample n=>fun i=>f i (w i)) :=
    Measurable.of_eval fun i=>(hf i).comp (measurable_pi_apply i)
  have hgg : Measurable (fun w : VectorBrownianSample n=>fun i=>g i (w i)) :=
    Measurable.of_eval fun i=>(hg i).comp (measurable_pi_apply i)
  have hadj:=indepFun_adjoin_initial (vectorBrownianMeasure n) (anisotropicMeasureOuterLaw D μ a)
    _ _ hfg hgg hten
  let record : AnisotropicDisorder n×(Fin n→Iic q→ℝ)→(Iic q→AnisotropicDisorder n×Field n) :=
    fun p s=>(p.1,WithLp.toLp 2 (fun i=>p.2 i s))
  have hr : Measurable record := by unfold record;fun_prop
  have hh:=hadj.comp measurable_id hr
  rw [anisotropicBrownianFiltration,Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp hh

end QuantitativeFollowup
