module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingApproximation
public import QuantitativeFollowup.FollowupCavityNativeTerminalApproximation

@[expose] public section

/-! Every genuinely finite profile, rather than only the canonical dyadic
profiles, has one exact finite recorded realization for all physical `u`.
The construction retains the original terminal test and every observation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreaming_finiteScheme_first_zero (μ : Paper.ParisiMeasure)
    (hμ : (μ:Measure Paper.Overlap).support.Finite) :
    (FRSB.finiteLawRSBScheme μ hμ).q 1=0 := by
  change FRSB.finiteLawSchemeOverlap μ hμ 1=0
  simpa [FRSB.finiteLawSchemeOverlap] using
    FRSB.finiteLawSchemeOverlap_zero μ hμ

theorem exists_finite_cavityStreamingAtom_finite_profile_representation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (a : ℝ) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C) :
    ∃(K : ℕ)(s : RSBScheme K)(A : CavityStreamingAtom n K),
      Paper.parisiSchemeMeasure s=μ ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      A.complexity=FiniteCascadeGenealogy.leafCount (asGenealogy T) ∧ A.bound=C ∧
      ∀u∈Icc (0:ℝ) 1,A.eval β ρ hβ hρ s a u=
        followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u := by
  let r:=FRSB.finiteLawRSBScheme μ hμ
  have hr:r.q 1=0:=nativeStreaming_finiteScheme_first_zero μ hμ
  have hm:Paper.parisiSchemeMeasure r=μ:=FRSB.parisiSchemeMeasure_finiteLawRSBScheme μ hμ
  have hf:a≤Paper.parisiCDF (Paper.parisiSchemeMeasure r) 0:=by
    rw [hm]
    exact hfloor
  obtain ⟨K,s,e,hs,hszero,has,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_floor_observation_scheme_embedding r hr a hf q hq J hJ hzero htop
  let d:=observationEmbeddingGaps e
  have hdepth:observationRefinementDepth d J=K+2:=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  have hl (j:ℕ):anisotropicRecordedSchemeSchedule s (observationRefinementDepth d j)=q j:=by
    rw [observationRefinementDepth_embedding e he hezero]
    exact hlevels j
  let U:=observationTreeDepthCast hdepth (observationRefineTree d T)
  let G:=fun σ : TerminalSpins (Configuration (n+1)) U=>
    F (observationRefinementTerminalProject d T hdepth σ)
  let A:CavityStreamingAtom n K:=
    { tree:=U
      test:=cavityTerminalSampleObservable U G
      bound:=C
      bound_nonneg:=hC
      test_le:=fun σ=>hF _ }
  refine ⟨K,s,A,hs.trans hm,hszero,has,?_,rfl,?_⟩
  · exact leafCount_observationRefinementDepthCast d T hdepth
  · intro u hu
    rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ _ a q T F u hu]
    have hmap:=anisotropicRecordedProfileTreeLaw_refined_scheme
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a q d hl T hdepth
    rw [hs,hm] at hmap
    change (anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a U).map
      (Prod.map id (observationRefinementDepthProject (S:=Configuration (n+1)) d T hdepth))=
      (anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a q T:Measure (CavityPathRecordSpace T (n+1))) at hmap
    change followupCavityPhysicalExpectation n β ρ hβ hρ s a U
      (cavityTerminalSampleObservable U G) u=_
    rw [followupCavityPhysicalExpectation_terminal_integral β ρ hβ hρ s a hszero U G u hu,←hmap]
    have hFm:Measurable (fun z:CavityPathRecordSpace T (n+1)=>F (finiteCascadeRecordTerminalSpins T z.2)):=
      (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
    rw [integral_map
      (measurable_id.prodMap (measurable_observationRefinementDepthProject d T hdepth)).aemeasurable
      hFm.aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall fun z=>congrArg F (observationRefinementTerminalProject_record d T hdepth z.2)

/-- Literal finite streaming for any actual finite profile and any fixed
physical observation tree, after the exact law-preserving refinement.
All six terms below are the genuine marked-law expectations. -/
theorem exists_native_finite_six_streaming_realization
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (hμ : (μ:Measure Paper.Overlap).support.Finite)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C) :
    ∃(K : ℕ)(s : RSBScheme K)(A : CavityStreamingAtom n K),
      Paper.parisiSchemeMeasure s=μ ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      A.complexity=FiniteCascadeGenealogy.leafCount (asGenealogy T) ∧ A.bound=C ∧
      (∀u∈Icc (0:ℝ) 1,A.eval β ρ hβ hρ s a u=
        followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u) ∧
      ∀(u:ℝ)(hu:u∈Icc (0:ℝ) 1),HasDerivWithinAt
        (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
        (followupCavityAlpha n β ρ/2*cavityMarkedSixExpectation
          (followupCavitySpinModel n β ρ hβ hρ u hu) s a A.tree
          (followupCavityPhysicalRecordObservable n A.tree A.test)) (Icc (0:ℝ) 1) u := by
  obtain ⟨K,s,A,hm,hs,has,hL,hB,he⟩:=
    exists_finite_cavityStreamingAtom_finite_profile_representation β ρ hβ hρ μ hμ
      a hfloor q hq hJ hzero htop T F C hC hF
  refine ⟨K,s,A,hm,hs,has,hL,hB,he,?_⟩
  intro u hu
  have hd:=hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed
    hn β ρ hβ hρ s a ha has hs A.tree A.test u hu
  exact hd.congr_of_mem (fun v hv=>(he v hv).symm) hu

end QuantitativeFollowup
