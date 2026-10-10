module
public import FourPapersCommon.BrownianClockRescaling
public import Paper.DiracShift
public import Paper.RSFunctional

@[expose] public section

/-! The whole continuous future Wiener path has its true Wiener law and
is independent of every measurable record in the original Brownian past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped NNReal Topology
namespace FourPapersCommon
set_option maxHeartbeats 900000

def canonicalFutureBrownianPath (a : ℝ≥0) (sample : BrownianSample) :
    C(Paper.Overlap,ℝ) where
  toFun t := canonicalBrownian (a+(t : ℝ).toNNReal) sample-canonicalBrownian a sample
  continuous_toFun := (((continuous_canonicalBrownian sample).comp
    (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))).sub
      continuous_const)

theorem measurable_canonicalFutureBrownianPath (a : ℝ≥0) :
    Measurable (canonicalFutureBrownianPath a) := by
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (measurable_canonicalBrownian _).sub (measurable_canonicalBrownian _)

@[simp] theorem canonicalFutureBrownianPath_zero (a : ℝ≥0) (sample : BrownianSample) :
    canonicalFutureBrownianPath a sample 0=0 := by
  change canonicalBrownian (a+(0 : ℝ).toNNReal) sample-canonicalBrownian a sample=0
  simp

theorem canonicalFutureBrownian_fullLaw (a : ℝ≥0) :
    canonicalBrownianMeasure.map
      (fun sample=>fun t : ℝ≥0=>canonicalBrownian (a+t) sample-canonicalBrownian a sample)=
      canonicalBrownianMeasure.map (fun sample=>fun t=>canonicalBrownian t sample) := by
  have hs := (isBrownianReal_canonicalBrownian.shift a).toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval fun t=>(measurable_canonicalBrownian _).sub
      (measurable_canonicalBrownian _)).aemeasurable
  have hb := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.hasLaw_gaussianLimit
    (Measurable.of_eval measurable_canonicalBrownian).aemeasurable
  exact hs.map_eq.trans hb.map_eq.symm

theorem canonicalFutureBrownianPath_law (a : ℝ≥0) :
    canonicalBrownianMeasure.map (canonicalFutureBrownianPath a)=canonicalWienerMeasure := by
  let R : (ℝ≥0→ℝ)→(Paper.Overlap→ℝ) := fun f t=>f (t : ℝ).toNNReal
  have hR : Measurable R := Measurable.of_eval fun _=>measurable_pi_apply _
  have hf : Measurable (fun sample=>fun t : ℝ≥0=>
      canonicalBrownian (a+t) sample-canonicalBrownian a sample) :=
    Measurable.of_eval fun t=>(measurable_canonicalBrownian (a+t)).sub
      (measurable_canonicalBrownian a)
  have he := congrArg (fun P=>P.map R) (canonicalFutureBrownian_fullLaw a)
  rw [Measure.map_map hR hf,
    Measure.map_map hR (Measurable.of_eval measurable_canonicalBrownian)] at he
  apply continuousRealPathMeasure_ext
  rw [Measure.map_map measurable_continuousRealPath_coe (measurable_canonicalFutureBrownianPath a)]
  change _=(canonicalBrownianMeasure.map canonicalBrownianPath).map _
  rw [Measure.map_map measurable_continuousRealPath_coe measurable_canonicalBrownianPath]
  exact he

theorem canonicalFutureBrownianPath_indep_past {A : Type*} [MeasurableSpace A]
    (a : ℝ≥0) (Y : BrownianSample→A) (hY : Measurable[canonicalBrownianFiltration a] Y) :
    IndepFun (canonicalFutureBrownianPath a) Y canonicalBrownianMeasure := by
  let R : (ℝ≥0→ℝ)→(Paper.Overlap→ℝ) := fun f t=>f (t : ℝ).toNNReal
  have hR : Measurable R := Measurable.of_eval fun _=>measurable_pi_apply _
  have hi := (isBrownianReal_canonicalBrownian.toIsPreBrownianReal.indepFun_shift a).comp
    hR measurable_id
  have hpath : (inferInstance : MeasurableSpace C(Paper.Overlap,ℝ))=
      MeasurableSpace.pi.comap (fun path : C(Paper.Overlap,ℝ)=>fun t=>path t) := by
    calc
      _ = ⨆t : Paper.Overlap,(inferInstance : MeasurableSpace ℝ).comap
          (fun path : C(Paper.Overlap,ℝ)=>path t) :=
        ProbabilityTheory.ContinuousMap.measurableSpace_eq_iSup_comap_eval
      _ = _ := by simp only [MeasurableSpace.pi,MeasurableSpace.comap_iSup,
        MeasurableSpace.comap_comp,Function.comp_def]
  have hpast : canonicalBrownianFiltration a=MeasurableSpace.pi.comap
      (fun sample=>fun t : Iic a=>canonicalBrownian t sample) :=
    Filtration.natural_eq_comap canonicalBrownian
      (fun t=>(measurable_canonicalBrownian t).stronglyMeasurable) a
  apply (IndepFun_iff_Indep _ _ _).mpr
  change Indep ((inferInstance : MeasurableSpace C(Paper.Overlap,ℝ)).comap
      (canonicalFutureBrownianPath a)) _ _
  rw [hpath,MeasurableSpace.comap_comp]
  have hi' := (IndepFun_iff_Indep _ _ _).mp hi
  dsimp only [Function.comp_def,id_eq] at hi'
  rw [←hpast] at hi'
  exact indep_of_indep_of_le_right hi' hY.comap_le

theorem canonicalFutureBrownianPath_joint_law {A : Type*} [MeasurableSpace A]
    (a : ℝ≥0) (Y : BrownianSample→A) (hY : Measurable[canonicalBrownianFiltration a] Y) :
    canonicalBrownianMeasure.map (fun sample=>(Y sample,canonicalFutureBrownianPath a sample))=
      (canonicalBrownianMeasure.map Y).prod canonicalWienerMeasure := by
  have hYm := hY.mono (canonicalBrownianFiltration.le a) le_rfl
  have he := (canonicalFutureBrownianPath_indep_past a Y hY).symm.map_prod_eq_prod_map_map
    hYm.aemeasurable (measurable_canonicalFutureBrownianPath a).aemeasurable
  rw [canonicalFutureBrownianPath_law] at he
  exact he

end FourPapersCommon
