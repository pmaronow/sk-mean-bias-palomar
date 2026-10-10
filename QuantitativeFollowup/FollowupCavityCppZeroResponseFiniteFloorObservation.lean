module
public import QuantitativeFollowup.AnisotropicRecordedObservationFloorAdapter
public import QuantitativeFollowup.AnisotropicRecordedBinaryFreshLaw
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! A genuine finite profile and any prescribed observation admit a
same-measure scheme with canonical right-CDF masses and the actual lower
floor. The observation and the zero root are retained exactly. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper
namespace QuantitativeFollowup
open SpinGlass.Targets
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

private theorem finiteFloor_binary_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p):=by
  apply antitone_nat_of_succ_le
  intro j
  cases j with
  | zero => exact p.property.2
  | succ j => cases j with
    | zero => exact p.property.1
    | succ j => exact le_refl _

theorem exists_cavity_zero_response_finite_floor_observation
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (a : ℝ) (hfloor : a≤Paper.parisiCDF μ 0) (p : Paper.Overlap) :
    ∃ (K : ℕ) (s : RSBScheme K) (d : ℕ) (hd : d≤K+2),
      Paper.parisiSchemeMeasure s=μ ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      anisotropicSchemeNode s (K+2-d) (by omega)=p:=by
  let r:=FRSB.finiteLawRSBScheme μ hμ
  have hr:r.q 1=0:=by
    change FRSB.finiteLawSchemeOverlap μ hμ 1=0
    simpa [FRSB.finiteLawSchemeOverlap] using FRSB.finiteLawSchemeOverlap_zero μ hμ
  have hm:Paper.parisiSchemeMeasure r=μ:=FRSB.parisiSchemeMeasure_finiteLawRSBScheme μ hμ
  have hf:a≤Paper.parisiCDF (Paper.parisiSchemeMeasure r) 0:=by
    rw [hm]
    exact hfloor
  obtain ⟨K,s,e,hs,hszero,has,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_floor_observation_scheme_embedding r hr a hf
      (anisotropicBinaryObservationSchedule p) (finiteFloor_binary_antitone p) 2
      (by norm_num) rfl rfl
  have hd:e 1≤K+2:=by
    have h:=he.monotone (show (1:ℕ)≤2 by omega)
    simpa only [hetop] using h
  refine ⟨K,s,e 1,hd,hs.trans hm,hszero,has,?_⟩
  have hnode:=hlevels 1
  change anisotropicFiniteMeshNode s (K+2-e 1)=p at hnode
  apply Subtype.ext
  exact (anisotropicFiniteMeshNode_coe s (K+2-e 1) (Nat.sub_le _ _)).symm.trans
    (congrArg Subtype.val hnode)

end QuantitativeFollowup
