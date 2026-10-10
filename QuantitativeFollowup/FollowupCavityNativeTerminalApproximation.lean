module
public import QuantitativeFollowup.FollowupCavityStreamingAtoms
public import QuantitativeFollowup.FollowupCavityNativeComparison

@[expose] public section

/-! Every grid profile has one fixed finite realization valid for the
whole physical interpolation interval. Weak convergence retains the
literal terminal test; no derivative convergence is postulated. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction ContDiff
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityNativeTerminalExpectation (n : ℕ) (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) : ℝ :=
  if hu : u∈Icc (0:ℝ) 1 then
    ∫z : CavityPathRecordSpace T (n+1), F (finiteCascadeRecordTerminalSpins T z.2)
      ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a q T : Measure (CavityPathRecordSpace T (n+1)))
  else 0

theorem followupCavityNativeTerminalExpectation_eq (β ρ : ℝ)
    (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u=
      ∫z : CavityPathRecordSpace T (n+1), F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a q T : Measure (CavityPathRecordSpace T (n+1))) := by
  simp only [followupCavityNativeTerminalExpectation,dif_pos hu]

theorem exists_finite_cavityStreamingAtom_grid_representation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀σ,|F σ|≤C) (N : ℕ) :
    ∃(K : ℕ)(s : RSBScheme K)(A : CavityStreamingAtom n K),
      Paper.parisiSchemeMeasure s=Paper.parisiGridMeasure μ N ∧ s.q 1=0 ∧ a ≤ s.m 1 ∧
      A.complexity=FiniteCascadeGenealogy.leafCount (asGenealogy T) ∧ A.bound=C ∧
      ∀u∈Icc (0:ℝ) 1,A.eval β ρ hβ hρ s a u=
        followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F u := by
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

theorem contDiffOn_followupCavityNativeTerminalExpectation_grid
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (N : ℕ) :
    ContDiffOn ℝ ∞ (followupCavityNativeTerminalExpectation n β ρ hβ hρ
      (Paper.parisiGridMeasure μ N) a q T F) (Icc (0:ℝ) 1) := by
  classical
  let C:=∑σ,|F σ|
  have hC:0≤C:=Finset.sum_nonneg (fun σ _=>abs_nonneg _)
  have hF (σ):|F σ|≤C:=Finset.single_le_sum (fun σ _=>abs_nonneg (F σ)) (Finset.mem_univ σ)
  obtain ⟨K,s,A,_,_,_,_,_,he⟩:=exists_finite_cavityStreamingAtom_grid_representation β ρ hβ hρ μ a hfloor
    q hq hJ hzero htop T F C hC hF N
  exact (contDiffOn_followupCavityPhysicalExpectation n β ρ hβ hρ s a A.tree A.test).congr
    (fun u hu=>(he u hu).symm)

theorem tendsto_followupCavityNativeTerminalExpectation_grid
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (u : ℝ) :
    Tendsto (fun N=>followupCavityNativeTerminalExpectation n β ρ hβ hρ
      (Paper.parisiGridMeasure μ N) a q T F u) atTop
      (𝓝 (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F u)) := by
  classical
  by_cases hu:u∈Icc (0:ℝ) 1
  · simp only [followupCavityNativeTerminalExpectation,dif_pos hu]
    let C:ℝ:=∑σ:TerminalSpins (Configuration (n+1)) T,‖F σ‖
    have hb (σ:TerminalSpins (Configuration (n+1)) T):‖F σ‖≤C:=
      Finset.single_le_sum (fun σ _=>norm_nonneg (F σ)) (Finset.mem_univ σ)
    let G:CavityPathRecordSpace T (n+1)→ᵇℝ:=BoundedContinuousFunction.mkOfBound
      ⟨fun z=>F (finiteCascadeRecordTerminalSpins T z.2),
        (continuous_of_discreteTopology (f:=F)).comp
          ((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_snd)⟩
      (2*C) (fun z w=>(dist_le_norm_add_norm _ _).trans
        ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_anisotropicRecordedEnergyProbability_grid
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T hq) G
  · simp only [followupCavityNativeTerminalExpectation,dif_neg hu]
    exact tendsto_const_nhds

end QuantitativeFollowup
