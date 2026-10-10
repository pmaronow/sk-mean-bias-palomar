module
public import QuantitativeFollowup.AnisotropicRecordedProfileTree
public import QuantitativeFollowup.AnisotropicFiniteMeasureStateAgreement
public import QuantitativeFollowup.AnisotropicVarianceRestartHistory

@[expose] public section

/-! Each actual fresh-noise continuation at an original finite observation
node is the normalized Gaussian continuation of that finite scheme. This
identifies the kernels pointwise in the initial disorder and field, including
repeated nodes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

theorem anisotropicFiniteRestartPhysicalKernel_at_node (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) :
    anisotropicFiniteRestartPhysicalKernel D s (anisotropicFiniteMeshNode s i) i=
      anisotropicFiniteTransition D s i := by
  let q:=anisotropicFiniteMeshNode s i
  have hq : (q:ℝ)=s.q i:=anisotropicFiniteMeshNode_coe s i (by omega)
  have hF : anisotropicFinitePotential D (vectorClampedScheme s q q.property) (k+1-i)=
      anisotropicFinitePotential D s (k+1-i) := by
    rw [←anisotropicTailRecursion_eq_clamped D s q q.property (by omega)]
    apply anisotropicTailRecursion_prefix_of_le D s q (by omega)
    rw [hq,show k+2-(k+1-i)=i+1 from by omega]
    exact s.q_mono i hi
  have hm : anisotropicSchemeMass (vectorClampedScheme s q q.property) (k+1+1-(i+1))=
      anisotropicSchemeMass s (k+1-i) := by
    unfold anisotropicSchemeMass
    rw [show k+1+1-(k+1+1-(i+1))=i+1 from by omega,vectorClampedScheme_mass_succ]
    congr 1
    omega
  have hL : anisotropicSchemeInput D (vectorClampedScheme s q q.property) (k+1+1-(i+1))=
      anisotropicSchemeInput D s (k+1-i) := by
    unfold anisotropicSchemeInput
    rw [show k+1+2-(k+1+1-(i+1))=(i+1)+1 from by omega,
      show k+1+1-(k+1+1-(i+1))=i+1 from by omega,
      vectorClampedScheme_overlap_succ,vectorClampedScheme_overlap_succ,hq,
      max_eq_right (s.q_mono i hi),max_self]
    rw [show k+2-(k+1-i)=i+1 from by omega,
      show k+1-(k+1-i)=i from by omega]
  unfold anisotropicFiniteRestartPhysicalKernel anisotropicFiniteTransition
  rw [hm,hL,show k+1+1-(i+1)=k+1-i from by omega,hF]

theorem anisotropicObservationTransition_scheme_parameter (D : AnisotropicSpinModel n)
    (s : RSBScheme k) (i : ℕ) (hi : i≤k+1) (z : AnisotropicObservationState n) :
    (anisotropicObservationTransition D (Paper.parisiSchemeMeasure s)
      (anisotropicFiniteMeshNode s i) (anisotropicFiniteMeshNode s (i+1)) z).map
        (anisotropicObservationParameter D)=
      anisotropicFiniteTransition D s i (anisotropicObservationParameter D z) := by
  let q:=anisotropicFiniteMeshNode s i
  let r:=anisotropicFiniteMeshNode s (i+1)
  let v : ℝ≥0:=(s.q (i+1)-s.q i).toNNReal
  have hq : (q:ℝ)=s.q i:=anisotropicFiniteMeshNode_coe s i (by omega)
  have hr : (r:ℝ)=s.q (i+1):=anisotropicFiniteMeshNode_coe s (i+1) (by omega)
  have hv : v≤vectorRestartHorizon q := by
    apply Real.toNNReal_le_toNNReal
    rw [hq]
    linarith [s.q_le_one (by omega : i+1≤k+2)]
  have hvcoe : (v:ℝ)=s.q (i+1)-s.q i :=
    Real.coe_toNNReal _ (sub_nonneg.mpr (s.q_mono i hi))
  have ht0 : anisotropicRestartElapsed s q i=0 := by
    simp only [anisotropicRestartElapsed,hq,max_self,sub_self,Real.toNNReal_zero]
  have ht1 : anisotropicRestartElapsed s q (i+1)=v := by
    simp only [anisotropicRestartElapsed,hq,max_eq_right (s.q_mono i hi),v]
  have hcanon : HasLaw
      (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2)
      (vectorWienerMeasure n) (vectorDisorderBrownianMeasure n) :=
    hasLaw_vectorCanonicalBrownianPath.comp (hasLaw_vectorBrownian_samples_with_disorder n)
  have hmz : Measurable (fun W : VectorWienerPath n=>((v:ℝ),(z,W))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hX := (measurable_uncurry_anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q).comp hmz
  have hpair:= (show Measurable (fun _ : VectorWienerPath n=>z.1) from measurable_const).prodMk hX
  have hf0 := (measurable_anisotropicObservationParameter D).comp hpair
  have hf : Measurable (fun W : VectorWienerPath n=>anisotropicObservationParameter D
      (z.1,anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q (z,W) (v:ℝ))) := by
    convert hf0 using 1
    rfl
  have ha0 := (measurable_anisotropicObservationNoiseAdvance D (Paper.parisiSchemeMeasure s) q r).comp
      ((show Measurable (fun _ : VectorWienerPath n=>z) from measurable_const).prodMk measurable_id)
  have ha : Measurable (fun W : VectorWienerPath n=>
      (z.1,anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q (z,W) ((r:ℝ)-(q:ℝ)))) := by
    convert ha0 using 1
    rfl
  have hcm : Measurable (fun p : VectorDisorderBrownianSample n=>vectorCanonicalBrownianPath p.2) := by
    simpa only [Function.comp_def] using (measurable_vectorCanonicalBrownianPath.comp measurable_snd)
  rw [anisotropicObservationTransition_apply,Measure.map_map
    (measurable_anisotropicObservationParameter D) ha]
  change (vectorWienerMeasure n).map
    (fun W=>anisotropicObservationParameter D
      (z.1,anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q (z,W)
        ((r:ℝ)-(q:ℝ))))=_
  rw [hq,hr,←hvcoe,←hcanon.map_eq,Measure.map_map (μ:=vectorDisorderBrownianMeasure n) hf hcm]
  have he : (fun p : VectorDisorderBrownianSample n=>
      anisotropicObservationParameter D
        (z.1,anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q
          (z,vectorCanonicalBrownianPath p.2) (v:ℝ)))=
      anisotropicFiniteRestartPhysicalParameter D s z.1 q z.2 v := by
    funext p
    rw [anisotropicRestartNoiseStatePath_canonical D (Paper.parisiSchemeMeasure s) z.1 q z.2 v hv p,
      anisotropicRestartState_scheme_eq_finite]
    rfl
  change (vectorDisorderBrownianMeasure n).map
    (fun p=>anisotropicObservationParameter D
      (z.1,anisotropicRestartNoiseStatePath D (Paper.parisiSchemeMeasure s) q
        (z,vectorCanonicalBrownianPath p.2) (v:ℝ)))=_
  rw [he]
  have hlaw:=anisotropicFiniteRestartPhysical_restricted_transition_law D s z.1 q z.2 i hi
    univ MeasurableSet.univ
  simp only [Measure.restrict_univ,ht0,ht1] at hlaw
  have hzero : anisotropicFiniteRestartPhysicalParameter D s z.1 q z.2 0=
      (fun _=>anisotropicObservationParameter D z) :=
    funext (anisotropicFiniteRestartPhysicalParameter_zero D s z.1 q z.2)
  have hinit : (vectorDisorderBrownianMeasure n).map
      (anisotropicFiniteRestartPhysicalParameter D s z.1 q z.2 0)=
      Measure.dirac (anisotropicObservationParameter D z) := by
    calc
      _=(vectorDisorderBrownianMeasure n).map (fun _=>anisotropicObservationParameter D z) :=
        congrArg (fun f : VectorDisorderBrownianSample n→AnisotropicParameter n=>
          (vectorDisorderBrownianMeasure n).map f) hzero
      _=_ := by simp only [Measure.map_const,measure_univ,one_smul]
  have hcomp:=congrArg (fun P : Measure (AnisotropicParameter n)=>
    anisotropicFiniteRestartPhysicalKernel D s q i ∘ₘ P) hinit
  have hd : anisotropicFiniteRestartPhysicalKernel D s q i ∘ₘ
      Measure.dirac (anisotropicObservationParameter D z)=
        anisotropicFiniteRestartPhysicalKernel D s q i (anisotropicObservationParameter D z) :=
    Measure.dirac_bind (Kernel.measurable _) _
  have hk:=congrArg (fun K : Kernel (AnisotropicParameter n) (AnisotropicParameter n)=>
    K (anisotropicObservationParameter D z)) (anisotropicFiniteRestartPhysicalKernel_at_node D s i hi)
  exact hlaw.trans (hcomp.trans (hd.trans hk))

end QuantitativeFollowup
