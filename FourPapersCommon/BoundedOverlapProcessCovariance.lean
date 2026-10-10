module
public import FourPapersCommon.EndpointFixedL2Compression
public import FourPapersCommon.HilbertCovarianceTrace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Analysis.Convex.Integral

public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! Actual bounded continuous overlap processes, their centered L²
random variables, and their covariance operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology ENNReal NNReal
namespace FourPapersCommon
instance overlapL2_measurableSpace (ν : Measure Paper.Overlap) :
    MeasurableSpace (Lp ℝ 2 ν):=borel _

instance overlapL2_borelSpace (ν : Measure Paper.Overlap) :
    BorelSpace (Lp ℝ 2 ν):=⟨rfl⟩

instance overlapL2_secondCountable (ν : Measure Paper.Overlap) [IsFiniteMeasure ν] :
    SecondCountableTopology (Lp ℝ 2 ν) := by
  have : Fact ((2:ℝ≥0∞)≠∞):=⟨by simp⟩
  infer_instance

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (ν : Measure Paper.Overlap) [IsFiniteMeasure ν]
variable (F : Ω→C(Paper.Overlap,ℝ))
set_option maxHeartbeats 1000000

def overlapProcessMean : C(Paper.Overlap,ℝ):=∫ω,F ω ∂P

def overlapCenteredPath (ω : Ω) : C(Paper.Overlap,ℝ):=
  F ω-overlapProcessMean P F

def overlapCenteredL2Process (ω : Ω) : Lp ℝ 2 ν:=
  ContinuousMap.toLp 2 ν ℝ (overlapCenteredPath P F ω)

def overlapCenteredEndpointProcess (ω : Ω) : endpointFixedL2 ν:=
  endpointFixedL2Compression ν (overlapCenteredL2Process P ν F ω)

theorem integrable_bounded_overlap_process (hF : Measurable F)
    (K : ℝ) (_hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) : Integrable F P:=
  (integrable_const K).mono' hF.aestronglyMeasurable (.of_forall hb)

theorem overlapProcessMean_apply (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) (q : Paper.Overlap) :
    overlapProcessMean P F q=∫ω,F ω q ∂P:=
  ContinuousMap.integral_apply (integrable_bounded_overlap_process P F hF K hK hb) q

theorem overlapProcessMean_norm_le (_hF : Measurable F)
    (K : ℝ) (_hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    ‖overlapProcessMean P F‖≤K := by
  exact (norm_integral_le_of_norm_le_const (.of_forall hb)).trans_eq (by simp)

omit [IsProbabilityMeasure P] in
theorem measurable_overlapCenteredL2Process (hF : Measurable F) :
    Measurable (overlapCenteredL2Process P ν F) :=
  (ContinuousMap.toLp 2 ν ℝ).continuous.measurable.comp
    (hF.sub measurable_const)

theorem memLp_overlapCenteredL2Process (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    MemLp (overlapCenteredL2Process P ν F) 2 P := by
  have hc : MemLp (overlapCenteredPath P F) 2 P := by
    apply MemLp.of_bound (hF.sub measurable_const).aestronglyMeasurable (2*K)
    exact .of_forall fun ω=>
      (norm_sub_le _ _).trans (by linarith [hb ω,overlapProcessMean_norm_le P F hF K hK hb])
  exact hc.continuousLinearMap_comp (ContinuousMap.toLp 2 ν ℝ)

omit [IsProbabilityMeasure P] in
theorem measurable_overlapCenteredEndpointProcess (hF : Measurable F) :
    Measurable (overlapCenteredEndpointProcess P ν F) :=
  (endpointFixedL2Compression ν).continuous.measurable.comp
    (measurable_overlapCenteredL2Process P ν F hF)

theorem memLp_overlapCenteredEndpointProcess (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    MemLp (overlapCenteredEndpointProcess P ν F) 2 P :=
  (memLp_overlapCenteredL2Process P ν F hF K hK hb).continuousLinearMap_comp
    (endpointFixedL2Compression ν)

omit [IsProbabilityMeasure P] in
theorem overlapCenteredL2Process_norm_sq (ω : Ω) :
    ‖overlapCenteredL2Process P ν F ω‖^2=
      ∫q,(F ω q-overlapProcessMean P F q)^2 ∂ν := by
  rw [←real_inner_self_eq_norm_sq]
  change inner ℝ (ContinuousMap.toLp 2 ν ℝ (overlapCenteredPath P F ω))
    (ContinuousMap.toLp 2 ν ℝ (overlapCenteredPath P F ω))=_
  rw [ContinuousMap.inner_toLp]
  congr 1
  ext q
  simp only [overlapCenteredPath,ContinuousMap.sub_apply,conj_trivial,pow_two]

theorem overlapCenteredL2Process_mem_endpoint (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    (hzero : ∀ω,F ω (0:Paper.Overlap)=0)
    (hone : ν {(1:Paper.Overlap)}=0) (ω : Ω) :
    overlapCenteredL2Process P ν F ω∈endpointFixedL2 ν := by
  apply (mem_endpointFixedL2_iff ν _).mpr
  have hne : ∀ᵐq : Paper.Overlap ∂ν,q≠1 := by
    rw [ae_iff]
    simpa only [not_not,ofPred_eq_eq_singleton] using hone
  filter_upwards [(overlapCenteredPath P F ω).coeFn_toLp (p:=2) (μ:=ν) (𝕜:=ℝ),hne]
    with q hq hne
  intro he
  change ((ContinuousMap.toLp 2 ν ℝ) (overlapCenteredPath P F ω)) q=0
  rw [hq]
  rcases he with he|he
  · have hq0 : q=(0:Paper.Overlap):=Subtype.ext he
    rw [hq0]
    change F ω 0-overlapProcessMean P F 0=0
    rw [hzero ω,overlapProcessMean_apply P F hF K hK hb]
    simp [hzero]
  · exact False.elim (hne (Subtype.ext he))

theorem overlapCenteredEndpointProcess_coe (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    (hzero : ∀ω,F ω (0:Paper.Overlap)=0)
    (hone : ν {(1:Paper.Overlap)}=0) (ω : Ω) :
    (overlapCenteredEndpointProcess P ν F ω : Lp ℝ 2 ν)=
      overlapCenteredL2Process P ν F ω := by
  exact congrArg Subtype.val (endpointFixedL2Compression_id ν
    ⟨_,overlapCenteredL2Process_mem_endpoint P ν F hF K hK hb hzero hone ω⟩)

def overlapProcessCovariance : endpointFixedL2 ν→L[ℝ]endpointFixedL2 ν:=
  covarianceOperator (P.map (overlapCenteredEndpointProcess P ν F))

def overlapFullProcessCovariance : Lp ℝ 2 ν→L[ℝ]Lp ℝ 2 ν:=
  covarianceOperator (P.map (overlapCenteredL2Process P ν F))

theorem overlapFullProcessCovariance_apply (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) (x : Lp ℝ 2 ν) :
    overlapFullProcessCovariance P ν F x=
      ∫ω,inner ℝ x (overlapCenteredL2Process P ν F ω) •
        overlapCenteredL2Process P ν F ω ∂P := by
  have hm := measurable_overlapCenteredL2Process P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredL2Process P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredL2Process P ν F hF K hK hb
  rw [overlapFullProcessCovariance,covarianceOperator_apply hi]
  have hci : Continuous (fun y : Lp ℝ 2 ν=>inner ℝ x y):=
    continuous_const.inner continuous_id
  have hc : Continuous (fun y : Lp ℝ 2 ν=>inner ℝ x y • y) := by
    convert hci.smul (continuous_id : Continuous (fun y : Lp ℝ 2 ν=>y)) using 1
    ext y
    rfl
  exact integral_map hm.aemeasurable hc.measurable.aestronglyMeasurable

theorem overlapFullProcessCovariance_range_endpoint (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    (hzero : ∀ω,F ω (0:Paper.Overlap)=0)
    (hone : ν {(1:Paper.Overlap)}=0) (x : Lp ℝ 2 ν) :
    overlapFullProcessCovariance P ν F x∈endpointFixedL2 ν := by
  rw [overlapFullProcessCovariance_apply P ν F hF K hK hb x]
  apply (endpointFixedL2 ν).convex.integral_mem (isClosed_endpointFixedL2 ν)
  · exact .of_forall fun ω=>(endpointFixedL2 ν).smul_mem _
      (overlapCenteredL2Process_mem_endpoint P ν F hF K hK hb hzero hone ω)
  · have hi := memLp_overlapCenteredL2Process P ν F hF K hK hb
    apply memLp_one_iff_integrable.mp
    convert ((hi.const_inner (𝕜:=ℝ) x).smul hi :
      MemLp ((fun ω=>inner ℝ x (overlapCenteredL2Process P ν F ω)) •
        overlapCenteredL2Process P ν F) 1 P) using 1

theorem integral_overlapCenteredL2Process (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    (∫ω,overlapCenteredL2Process P ν F ω ∂P)=0 := by
  have hi := (integrable_bounded_overlap_process P F hF K hK hb).sub
    (integrable_const (overlapProcessMean P F))
  change (∫ω,(ContinuousMap.toLp 2 ν ℝ) (overlapCenteredPath P F ω) ∂P)=0
  unfold overlapCenteredPath
  change (∫ω,(ContinuousMap.toLp 2 ν ℝ)
    ((F-(fun _ : Ω=>overlapProcessMean P F) : Ω→C(Paper.Overlap,ℝ)) ω) ∂P)=0
  rw [ContinuousLinearMap.integral_comp_comm _ hi]
  have hz : (∫ω,overlapCenteredPath P F ω ∂P)=0 := by
    change (∫ω,F ω-overlapProcessMean P F ∂P)=0
    rw [integral_sub
      (integrable_bounded_overlap_process P F hF K hK hb) (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul,overlapProcessMean,sub_self]
  change (ContinuousMap.toLp 2 ν ℝ) (∫ω,overlapCenteredPath P F ω ∂P)=0
  rw [hz,map_zero]

theorem overlapFullProcessCovariance_hasFinitePositiveTrace (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    HasFinitePositiveTrace (overlapFullProcessCovariance P ν F)
      (∫ω,‖overlapCenteredL2Process P ν F ω‖^2 ∂P) := by
  have hm := measurable_overlapCenteredL2Process P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredL2Process P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredL2Process P ν F hF K hK hb
  have ht := covarianceOperator_hasFinitePositiveTrace _ hi
  rw [integral_map (f:=fun x : Lp ℝ 2 ν=>‖x‖^2) hm.aemeasurable
    (continuous_norm.pow 2).measurable.aestronglyMeasurable] at ht
  exact ht

theorem overlapFullProcessCovariance_isPositiveTraceClass (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    IsPositiveTraceClass (overlapFullProcessCovariance P ν F) := by
  have hm := measurable_overlapCenteredL2Process P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredL2Process P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredL2Process P ν F hF K hK hb
  exact covarianceOperator_isPositiveTraceClass _ hi

theorem overlapProcessCovariance_hasFinitePositiveTrace (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    HasFinitePositiveTrace (overlapProcessCovariance P ν F)
      (∫ω,‖overlapCenteredEndpointProcess P ν F ω‖^2 ∂P) := by
  have hm := measurable_overlapCenteredEndpointProcess P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredEndpointProcess P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredEndpointProcess P ν F hF K hK hb
  have ht := covarianceOperator_hasFinitePositiveTrace _ hi
  rw [integral_map (f:=fun x : endpointFixedL2 ν=>‖x‖^2) hm.aemeasurable
    (continuous_norm.pow 2).measurable.aestronglyMeasurable] at ht
  exact ht

theorem overlapProcessCovariance_isPositiveTraceClass (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K) :
    IsPositiveTraceClass (overlapProcessCovariance P ν F) := by
  have hm := measurable_overlapCenteredEndpointProcess P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredEndpointProcess P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredEndpointProcess P ν F hF K hK hb
  exact covarianceOperator_isPositiveTraceClass _ hi

theorem overlapProcessCovariance_inner (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    (x y : endpointFixedL2 ν) :
    inner ℝ (overlapProcessCovariance P ν F x) y=
      ∫ω,inner ℝ x (overlapCenteredEndpointProcess P ν F ω)*
        inner ℝ y (overlapCenteredEndpointProcess P ν F ω) ∂P := by
  have hm := measurable_overlapCenteredEndpointProcess P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredEndpointProcess P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredEndpointProcess P ν F hF K hK hb
  rw [overlapProcessCovariance,covarianceOperator_inner hi]
  exact integral_map hm.aemeasurable
    (((continuous_const.inner continuous_id).mul
      (continuous_const.inner continuous_id)).measurable.aestronglyMeasurable)

theorem overlapProcessCovariance_trace_pairing (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ (endpointFixedL2 ν))
    (J : endpointFixedL2 ν→L[ℝ]endpointFixedL2 ν) :
    (∑'i,inner ℝ (overlapProcessCovariance P ν F (b i)) (J (b i)))=
      ∫ω,inner ℝ (overlapCenteredEndpointProcess P ν F ω)
        (J (overlapCenteredEndpointProcess P ν F ω)) ∂P := by
  have hm := measurable_overlapCenteredEndpointProcess P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredEndpointProcess P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredEndpointProcess P ν F hF K hK hb
  rw [overlapProcessCovariance,covarianceOperator_trace_pairing _ hi b J]
  exact integral_map hm.aemeasurable
    ((continuous_id.inner J.continuous).measurable.aestronglyMeasurable)

theorem overlapProcessCovariance_hasSum_comp_diagonal (hF : Measurable F)
    (K : ℝ) (hK : 0≤K) (hb : ∀ω,‖F ω‖≤K)
    {ι : Type*} [Countable ι] (b : HilbertBasis ι ℝ (endpointFixedL2 ν))
    (J : endpointFixedL2 ν→L[ℝ]endpointFixedL2 ν) :
    HasSum (fun i=>inner ℝ (J (overlapProcessCovariance P ν F (b i))) (b i))
      (∫ω,inner ℝ (overlapCenteredEndpointProcess P ν F ω)
        (J (overlapCenteredEndpointProcess P ν F ω)) ∂P) := by
  have hm := measurable_overlapCenteredEndpointProcess P ν F hF
  have hi : MemLp id 2 (P.map (overlapCenteredEndpointProcess P ν F)) := by
    apply (memLp_map_measure_iff measurable_id.aestronglyMeasurable hm.aemeasurable).mpr
    exact memLp_overlapCenteredEndpointProcess P ν F hF K hK hb
  have ht := covarianceOperator_hasSum_comp_diagonal _ hi b J
  rw [integral_map (f:=fun x : endpointFixedL2 ν=>inner ℝ x (J x)) hm.aemeasurable
    ((continuous_id.inner J.continuous).measurable.aestronglyMeasurable)] at ht
  exact ht

end FourPapersCommon
