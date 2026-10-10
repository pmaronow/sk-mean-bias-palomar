module
public import QuantitativePaper.VectorBrownianFiltration
public import FourPapersCommon.CanonicalBrownianFuture
public import Mathlib.MeasureTheory.Function.FactorsThrough

@[expose] public section

/-! The actual complete future vector Wiener path is independent of the
raw natural past, including initial disorder. The whole observed unit path
generates the actual raw time-one sigma-field. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal ENNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 600000
set_option maxSynthPendingDepth 128
variable {n:ℕ}

abbrev VectorWienerPath (n:ℕ):=Fin n→C(Paper.Overlap,ℝ)

def vectorWienerMeasure (n:ℕ):Measure (VectorWienerPath n):=
  Measure.pi (fun _=>Paper.canonicalWienerMeasure)

instance vectorWienerMeasure_probability (n:ℕ):IsProbabilityMeasure (vectorWienerMeasure n):=by
  unfold vectorWienerMeasure
  infer_instance

def vectorCanonicalBrownianPath (sample:VectorBrownianSample n):VectorWienerPath n:=
  fun i=>Paper.canonicalBrownianPath (sample i)

theorem measurable_vectorCanonicalBrownianPath :Measurable (vectorCanonicalBrownianPath (n:=n)):=
  Measurable.of_eval fun i=>Paper.measurable_canonicalBrownianPath.comp (measurable_pi_apply i)

theorem hasLaw_vectorCanonicalBrownianPath :
    HasLaw (vectorCanonicalBrownianPath (n:=n)) (vectorWienerMeasure n) (vectorBrownianMeasure n):=by
  refine ⟨measurable_vectorCanonicalBrownianPath.aemeasurable,?_⟩
  exact Measure.pi_map_pi (fun _=>Paper.measurable_canonicalBrownianPath.aemeasurable)

def vectorObservedBrownianPath (sample:VectorDisorderBrownianSample n):
    (Couplings n×ℝ)×VectorWienerPath n:=
  (sample.1,vectorCanonicalBrownianPath sample.2)

theorem measurable_vectorObservedBrownianPath :Measurable (vectorObservedBrownianPath (n:=n)):=
  measurable_fst.prodMk (measurable_vectorCanonicalBrownianPath.comp measurable_snd)

theorem hasLaw_vectorObservedBrownianPath :
    HasLaw (vectorObservedBrownianPath (n:=n))
      ((completionLaw n).prod (vectorWienerMeasure n)) (vectorDisorderBrownianMeasure n):=by
  refine ⟨measurable_vectorObservedBrownianPath.aemeasurable,?_⟩
  change ((completionLaw n).prod (vectorBrownianMeasure n)).map
    (Prod.map id vectorCanonicalBrownianPath)=_
  rw [←Measure.map_prod_map _ _ measurable_id measurable_vectorCanonicalBrownianPath,
    Measure.map_id,hasLaw_vectorCanonicalBrownianPath.map_eq]

def vectorFutureBrownianPath (a:ℝ≥0) (sample:VectorDisorderBrownianSample n):VectorWienerPath n:=
  fun i=>canonicalFutureBrownianPath a (sample.2 i)

theorem measurable_vectorFutureBrownianPath (a:ℝ≥0):Measurable (vectorFutureBrownianPath (n:=n) a):=
  Measurable.of_eval fun i=>(measurable_canonicalFutureBrownianPath a).comp
    ((measurable_pi_apply i).comp measurable_snd)

theorem hasLaw_vectorFutureBrownianPath (a:ℝ≥0):
    HasLaw (vectorFutureBrownianPath (n:=n) a) (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n):=by
  let f:VectorBrownianSample n→VectorWienerPath n:=fun w i=>canonicalFutureBrownianPath a (w i)
  have hf:Measurable f:=Measurable.of_eval fun i=>(measurable_canonicalFutureBrownianPath a).comp
    (measurable_pi_apply i)
  have hp:(vectorBrownianMeasure n).map f=vectorWienerMeasure n:=by
    rw [vectorBrownianMeasure,Measure.pi_map_pi (fun _=>(measurable_canonicalFutureBrownianPath a).aemeasurable)]
    simp only [canonicalFutureBrownianPath_law]
    rfl
  have hh:HasLaw f (vectorWienerMeasure n) (vectorBrownianMeasure n):=⟨hf.aemeasurable,hp⟩
  exact hh.comp (hasLaw_vectorBrownian_samples_with_disorder n)

theorem indep_vectorFutureBrownianPath_past (a:ℝ≥0):
    IndepFun (vectorFutureBrownianPath (n:=n) a)
      (fun sample:VectorDisorderBrownianSample n=>fun s:Iic a=>vectorBrownianRecord s sample)
      (vectorDisorderBrownianMeasure n):=by
  let f:Fin n→Paper.BrownianSample→C(Paper.Overlap,ℝ):=fun _=>canonicalFutureBrownianPath a
  let g:Fin n→Paper.BrownianSample→(Iic a→ℝ):=fun _=>scalarBrownianPast a
  have hf:∀i,Measurable (f i):=fun _=>measurable_canonicalFutureBrownianPath a
  have hg:∀i,Measurable (g i):=fun _=>measurable_scalarBrownianPast a
  have hsg:Measurable[Paper.canonicalBrownianFiltration a] (scalarBrownianPast a):=by
    letI:MeasurableSpace Paper.BrownianSample:=Paper.canonicalBrownianFiltration a
    exact Measurable.of_eval fun s=>((Filtration.stronglyAdapted_natural
      (fun u=>(Paper.measurable_canonicalBrownian u).stronglyMeasurable) s).mono
        (Paper.canonicalBrownianFiltration.mono s.property)).measurable
  have hten:=indepFun_finiteProduct (fun _:Fin n=>Paper.canonicalBrownianMeasure)
    f g hf hg (fun _=>canonicalFutureBrownianPath_indep_past a _ hsg)
  have hfg:Measurable (fun w:VectorBrownianSample n=>fun i=>f i (w i)):=
    Measurable.of_eval fun i=>(hf i).comp (measurable_pi_apply i)
  have hgg:Measurable (fun w:VectorBrownianSample n=>fun i=>g i (w i)):=
    Measurable.of_eval fun i=>(hg i).comp (measurable_pi_apply i)
  have hadj:=indepFun_adjoin_initial (vectorBrownianMeasure n) (completionLaw n) _ _ hfg hgg hten
  let record:(Couplings n×ℝ)×(Fin n→Iic a→ℝ)→(Iic a→VectorState n):=
    fun p s=>(p.1,WithLp.toLp 2 (fun i=>p.2 i s))
  have hr:Measurable record:=by unfold record;fun_prop
  exact hadj.comp measurable_id hr

theorem indep_vectorFutureBrownianPath_filtration (a:ℝ≥0):
    Indep (MeasurableSpace.comap (vectorFutureBrownianPath (n:=n) a) inferInstance)
      (vectorBrownianFiltration n a) (vectorDisorderBrownianMeasure n):=by
  rw [vectorBrownianFiltration,Filtration.natural_eq_comap]
  exact (IndepFun_iff_Indep _ _ _).mp (indep_vectorFutureBrownianPath_past a)

theorem indep_vectorFutureBrownianPath_known {A:Type*} [MeasurableSpace A]
    (a:ℝ≥0) (Z:VectorDisorderBrownianSample n→A)
    (hZ:Measurable[vectorBrownianFiltration n a] Z):
    IndepFun (vectorFutureBrownianPath a) Z (vectorDisorderBrownianMeasure n):=
  (IndepFun_iff_Indep _ _ _).mpr
    (indep_of_indep_of_le_right (indep_vectorFutureBrownianPath_filtration a) hZ.comap_le)

theorem measurable_vectorObservedBrownianPath_past_one :
    Measurable[vectorBrownianFiltration n 1] (vectorObservedBrownianPath (n:=n)):=by
  letI:MeasurableSpace (VectorDisorderBrownianSample n):=vectorBrownianFiltration n 1
  have hp:Measurable (fun sample:VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath sample.2):=by
    apply Measurable.of_eval
    intro i
    rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
    intro q
    have hr:(q:ℝ).toNNReal≤1:=by simpa using Real.toNNReal_le_toNNReal q.property.2
    have hm:=((stronglyAdapted_disorderVectorBrownian n (q:ℝ).toNNReal).mono
      ((vectorBrownianFiltration n).mono hr)).measurable
    exact ((EuclideanSpace.proj i).measurable.comp hm)
  exact (stronglyMeasurable_initialVectorDisorder n 1).measurable.prodMk hp

theorem vectorBrownianFiltration_one_eq_observedPath :
    vectorBrownianFiltration n 1=MeasurableSpace.comap (vectorObservedBrownianPath (n:=n)) inferInstance:=by
  apply le_antisymm
  · rw [vectorBrownianFiltration,Filtration.natural_eq_comap]
    let m:=MeasurableSpace.comap (vectorObservedBrownianPath (n:=n)) inferInstance
    have hpath:@Measurable _ _ m _ (vectorObservedBrownianPath (n:=n)):=Measurable.of_comap_le le_rfl
    have hh:@Measurable _ _ m _ (fun sample:VectorDisorderBrownianSample n=>
        fun r:Iic (1:ℝ≥0)=>vectorBrownianRecord r sample):=by
      apply Measurable.of_eval
      intro r
      let q:Paper.Overlap:=⟨(r:ℝ≥0),⟨r.val.coe_nonneg,by exact_mod_cast r.property⟩⟩
      have hfield:@Measurable _ _ m _ (fun sample:VectorDisorderBrownianSample n=>
          WithLp.toLp 2 (fun i=>(vectorObservedBrownianPath sample).2 i q)):=by
        apply (show Measurable (WithLp.toLp 2:(Fin n→ℝ)→Field n) from by fun_prop).comp
        exact Measurable.of_eval fun i=>
          (ContinuousMap.measurable_eval q).comp ((measurable_pi_apply i).comp hpath.snd)
      convert hpath.fst.prodMk hfield using 1
      funext sample
      congr 1
      ext i
      simp only [vectorObservedBrownianPath,vectorCanonicalBrownianPath,Paper.canonicalBrownianPath,
        q,Real.toNNReal_coe,vectorBrownianRecord,disorderVectorBrownian,vectorBrownian_apply]
    exact hh.comap_le
  · exact measurable_vectorObservedBrownianPath_past_one.comap_le

end QuantitativePaper
