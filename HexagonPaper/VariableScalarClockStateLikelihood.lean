module
public import HexagonPaper.VariableScalarClockState
public import HexagonPaper.VariableScalarClockPathDensity

@[expose] public section

/-! The actual Picard function of a continuous Itô noise inherits the
literal prefix and marked-joint likelihoods from the proved clock law.
The coefficient construction below discharges the noise-law hypothesis. -/
noncomputable section
open Set Filter MeasureTheory Paper FRSB FourPapersCommon ProbabilityTheory
open QuantitativeFollowup QuantitativePaper
open scoped Topology ENNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

def scalarClockStopMap (q : Paper.Overlap) : C(Paper.Overlap,Paper.Overlap) :=
  ⟨fun r=>min r q,continuous_id.min continuous_const⟩

def scalarClockPathStop (q : Paper.Overlap) (Z : C(Paper.Overlap,ℝ)) : C(Paper.Overlap,ℝ) :=
  Z.comp (scalarClockStopMap q)

theorem measurable_scalarClockPathStop (q : Paper.Overlap) :
    Measurable (scalarClockPathStop q) :=
  (ContinuousMap.compCLM ℝ ℝ (scalarClockStopMap q)).continuous.measurable

theorem scalarClockReferencePath_stop (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarClockPathStop q (scalarClockStoppedReferencePath τ β 1 sample)=
      scalarClockStoppedReferencePath τ β q sample := by
  ext r
  change scalarClockStoppedReferencePath τ β 1 sample (min r q)=_
  rw [scalarClockStoppedReferencePath_apply,scalarClockStoppedReferencePath_apply]
  have hm:min (min r q) (1:Paper.Overlap)=min r q:=by
    apply min_eq_left
    exact (min r q).property.2
  rw [hm]

theorem scalarClockStatePath_stop (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (μ : Paper.ParisiMeasure) (q : Paper.Overlap) (sample : Paper.BrownianSample) :
    scalarClockPathStop q (scalarClockStoppedStatePath τ β μ 1 sample)=
      scalarClockStoppedStatePath τ β μ q sample := by
  ext r
  change optimalStateReal β (scalarClockMeasure τ μ) sample
    (min (τ (min r q):ℝ) (τ (1:Paper.Overlap):ℝ).toNNReal)=
    optimalStateReal β (scalarClockMeasure τ μ) sample
      (min (τ r:ℝ) (τ q:ℝ).toNNReal)
  rw [scalarClock_one,show (((1:Paper.Overlap):ℝ).toNNReal)=1 by norm_num]
  rw [NNReal.coe_one,min_eq_left (τ (min r q)).property.2,
    Real.coe_toNNReal _ (τ q).property.1]
  congr 1
  exact congrArg Subtype.val (τ.monotone.map_min (a:=r) (b:=q))

theorem scalarClockStateFromNoise_likelihood
    (L : Paper.BrownianSample→C(Paper.Overlap,ℝ)) (hL : Measurable L)
    (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (q : Paper.Overlap)
    (hLaw : canonicalBrownianMeasure.map L=
      canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1)) :
    canonicalBrownianMeasure.map
      (fun sample=>scalarClockPathStop q (scalarClockStateFromNoise τ β μ (L sample)))=
      (canonicalBrownianMeasure.map (fun sample=>scalarClockPathStop q (L sample))).withDensity
        (scalarClockPrefixPathDensity τ β μ q) := by
  have hS : Measurable (fun Z:C(Paper.Overlap,ℝ)=>
      scalarClockPathStop q (scalarClockStateFromNoise τ β μ Z)):=
    (measurable_scalarClockPathStop q).comp (continuous_scalarClockStateFromNoise τ β μ).measurable
  have hstate:=congrArg (fun P:Measure C(Paper.Overlap,ℝ)=>P.map
    (fun Z=>scalarClockPathStop q (scalarClockStateFromNoise τ β μ Z))) hLaw
  rw [Measure.map_map hS hL,Measure.map_map hS
    (measurable_scalarClockStoppedReferencePath τ β 1)] at hstate
  simp only [Function.comp_def,scalarClockStateFromNoise_reference τ β hβ μ,scalarClockStatePath_stop] at hstate
  have hnoise:=congrArg (fun P:Measure C(Paper.Overlap,ℝ)=>P.map (scalarClockPathStop q)) hLaw
  rw [Measure.map_map (measurable_scalarClockPathStop q) hL,
    Measure.map_map (measurable_scalarClockPathStop q)
      (measurable_scalarClockStoppedReferencePath τ β 1)] at hnoise
  simp only [Function.comp_def,scalarClockReferencePath_stop] at hnoise
  rw [hstate,hnoise]
  exact scalarClockStoppedPath_likelihood_path τ β hβ μ q

theorem scalarClockMarkedSpinLaw_path_compProd (τ : Paper.Overlap≃oPaper.Overlap)
    (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) :
    (scalarMarkedSpinLaw β hβ (scalarClockMeasure τ μ)).map
      (fun p=>(scalarClockStoppedStatePath τ β μ 1 p.1,p.2))=
      (canonicalBrownianMeasure.map (scalarClockStoppedStatePath τ β μ 1)) ⊗ₘ scalarFullPathSpinKernel := by
  have hm:Measurable (scalarClockStoppedStatePath τ β μ 1):=by
    unfold scalarClockStoppedStatePath
    rw [scalarClock_one,show (((1:Paper.Overlap):ℝ).toNNReal)=1 by norm_num]
    exact (measurable_scalarClockPathReindex τ).comp
      (measurable_scalarStoppedStatePath β hβ (scalarClockMeasure τ μ) 1 (by norm_num))
  have he:=compProd_comap_map_history canonicalBrownianMeasure
    (scalarClockStoppedStatePath τ β μ 1) hm scalarFullPathSpinKernel
  have hk:scalarFullPathSpinKernel.comap (scalarClockStoppedStatePath τ β μ 1) hm=
      scalarTerminalSpinKernel β hβ (scalarClockMeasure τ μ) := by
    ext sample : 1
    change scalarSpinLaw (scalarClockStoppedStatePath τ β μ 1 sample 1)=
      scalarSpinLaw (parisiPhysicalSplitState β 0 (scalarClockMeasure τ μ) 1 sample)
    unfold scalarClockStoppedStatePath scalarClockPathReindex
    change scalarSpinLaw (scalarStoppedStatePath β (scalarClockMeasure τ μ)
      (τ (1:Paper.Overlap):ℝ).toNNReal sample (τ (1:Paper.Overlap)))=_
    rw [scalarClock_one,show (((1:Paper.Overlap):ℝ).toNNReal)=1 by norm_num,
      scalarStoppedStatePath_terminal β hβ]
  rw [hk] at he
  exact he

theorem scalarClockStateFromNoise_joint_likelihood
    (L : Paper.BrownianSample→C(Paper.Overlap,ℝ)) (hL : Measurable L)
    (τ : Paper.Overlap≃oPaper.Overlap) (β : ℝ) (hβ : β≠0)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (hLaw : canonicalBrownianMeasure.map L=
      canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1)) :
    (canonicalBrownianMeasure.map (fun sample=>scalarClockStateFromNoise τ β μ (L sample)))
      ⊗ₘ scalarFullPathSpinKernel=
      ((canonicalBrownianMeasure.map L).prod (Measure.count:Measure Bool)).withDensity
        (scalarClockJointPathDensity τ β μ a) := by
  have hS:Measurable (scalarClockStateFromNoise τ β μ):=
    (continuous_scalarClockStateFromNoise τ β μ).measurable
  have hstate:=congrArg (fun P:Measure C(Paper.Overlap,ℝ)=>P.map
    (scalarClockStateFromNoise τ β μ)) hLaw
  rw [Measure.map_map hS hL,Measure.map_map hS
    (measurable_scalarClockStoppedReferencePath τ β 1)] at hstate
  simp only [Function.comp_def,scalarClockStateFromNoise_reference τ β hβ μ] at hstate
  rw [hstate,hLaw,←scalarClockMarkedSpinLaw_path_compProd τ β hβ μ]
  have he:=scalarClockMarkedSpinLaw_likelihood_path τ β hβ μ a ha hμ
  have hprod:=Measure.map_prod_map canonicalBrownianMeasure (Measure.count:Measure Bool)
    (measurable_scalarClockStoppedReferencePath τ β 1) measurable_id
  rw [Measure.map_id] at hprod
  change (canonicalBrownianMeasure.map (scalarClockStoppedReferencePath τ β 1)).prod
    (Measure.count:Measure Bool)=
      (canonicalBrownianMeasure.prod (Measure.count:Measure Bool)).map
        (fun p=>(scalarClockStoppedReferencePath τ β 1 p.1,p.2)) at hprod
  rw [←hprod] at he
  simpa only [Measure.map_id] using he

end HexagonPaper
