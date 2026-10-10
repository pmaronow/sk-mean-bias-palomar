module
public import QuantitativeFollowup.FollowupCavityObservationPairGeometry

@[expose] public section

/-! A fixed finite observation realization preserves the actual old pair
and every branch level, throughout the full interpolation interval. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem exists_finite_cavityStreamingAtom_grid_pair_representation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C)
    (i l : ObservationLeaf T)
    (hdom : ∀σ,|F σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel T i l))
      (observationLeafTerminalSpin T i σ) (observationLeafTerminalSpin T l σ)|) (N : ℕ) :
    ∃(K : ℕ)(s : RSBScheme K)(A : CavityStreamingAtom n K)
      (i' l' : ObservationLeaf (trimRoot A.tree)),
      Paper.parisiSchemeMeasure s=Paper.parisiGridMeasure μ N ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      A.complexity=FiniteCascadeGenealogy.leafCount (asGenealogy T) ∧ A.bound=C ∧
      (∀u∈Icc (0:ℝ) 1,A.eval β ρ hβ hρ s a u=
        followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F u) ∧
      (∀r : CavityPathRecordSpace (trimRoot A.tree) (n+1),
        |followupCavityPhysicalRecordObservable n A.tree A.test r|≤
          |cavityRecordedLeafPairDefect s (trimRoot A.tree) i' l' r.2|) ∧
      (∀χ : Paper.Overlap→ℝ,finiteCascadeUnweightedBranchSum (fun j=>χ (cavityProfileLevel s j))
        (trimRoot A.tree)=finiteCascadeUnweightedBranchSum (fun j=>χ (q j)) T) := by
  let r:=Paper.parisiGridRSBScheme μ N
  have hr:r.q 1=0:=Paper.parisiGridSchemeOverlap_one N
  have hm:Paper.parisiSchemeMeasure r=Paper.parisiGridMeasure μ N:=FRSB.parisiSchemeMeasure_grid_eq μ N
  have hf:a≤Paper.parisiCDF (Paper.parisiSchemeMeasure r) 0:=by
    rw [hm,←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass,zeroMass_eq_parisiCDF_zero]
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
  refine ⟨K,s,A,cavityObservationRefinedLeaf d T hdepth i,
    cavityObservationRefinedLeaf d T hdepth l,hs.trans hm,hszero,has,?_,rfl,?_,?_,?_⟩
  · exact leafCount_observationRefinementDepthCast d T hdepth
  · intro u hu
    rw [followupCavityNativeTerminalExpectation_eq β ρ hβ hρ _ a q T F u hu]
    have hmap:=anisotropicRecordedProfileTreeLaw_refined_scheme
      (followupCavitySpinModel n β ρ hβ hρ u hu) s a q d hl T hdepth
    rw [hs,hm] at hmap
    change (anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a U).map
      (Prod.map id (observationRefinementDepthProject (S:=Configuration (n+1)) d T hdepth))=
      (anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
        (Paper.parisiGridMeasure μ N) a q T:Measure (CavityPathRecordSpace T (n+1))) at hmap
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

  · intro z
    letI : MeasurableSpace (TerminalSpins (Configuration (n+1)) U) :=
      terminalSpinMeasurableSpace (Configuration (n+1)) U
    letI : MeasurableSpace (FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy U)) :=
      FiniteCascadeGenealogy.sampleMeasurableSpace (Configuration (n+1)) (asGenealogy U)
    let σ : TerminalSpins (Configuration (n+1)) (trimRoot U):=
      finiteCascadeRecordTerminalSpins (trimRoot U) z.2
    let e := terminalSampleEquiv (S:=Configuration (n+1)) U
    let η:TerminalSpins (Configuration (n+1)) U:=
      (@MeasurableEquiv.symm (TerminalSpins (Configuration (n+1)) U)
        (FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy U))
        (terminalSpinMeasurableSpace (Configuration (n+1)) U)
        (FiniteCascadeGenealogy.sampleMeasurableSpace (Configuration (n+1)) (asGenealogy U)) e)
        (trimmedSpinEquiv (S:=Configuration (n+1)) U (terminalSampleEquiv (S:=Configuration (n+1)) (trimRoot U) σ))
    have hh:=hdom (observationRefinementTerminalProject d T hdepth η)
    have hi:=cavityObservationRefinedLeaf_terminalSpin (S:=Configuration (n+1)) d T hdepth i σ
    have hl':=cavityObservationRefinedLeaf_terminalSpin (S:=Configuration (n+1)) d T hdepth l σ
    dsimp only [η,e] at hh
    rw [hi,hl',observationLeafTerminalSpin_record,observationLeafTerminalSpin_record] at hh
    rw [←cavityObservationRefinedLeaf_profileLevel s hszero d T hdepth q hl i l] at hh
    change |F (observationRefinementTerminalProject d T hdepth η)|≤_ at hh
    convert! hh using 1 <;>
      simp only [A,followupCavityPhysicalRecordObservable,cavityTerminalSampleObservable,G,η,e,σ,
      terminalSampleEquiv_recordSpins]
  · intro χ
    exact cavityObservationRefined_branchSum s hszero d T hdepth q hl χ

end QuantitativeFollowup
