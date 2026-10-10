module
public import QuantitativeFollowup.FollowupCavityPositiveComparison
public import QuantitativeFollowup.AnisotropicRecordedObservationApproximation
public import FourPapersCommon.FiniteObservationTerminalProjection

@[expose] public section

/-! Positive terminal observables under the genuine fixed-observation
native cavity law obey the finite streaming comparison. Exact observation
refinements preserve the profile floor and every terminal mark. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2100000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFiniteRecorded_positive_spin_comparison
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (s:RSBScheme k)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(has:a ≤ s.m 1)(hq:s.q 1=0)
    (T:FiniteTerminalGenealogy (k+2))
    (F:TerminalSpins (Configuration (n+1)) T→ℝ)(hF0:∀σ,0≤F σ)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) 1)(hv:v∈Icc (0:ℝ) 1):
    (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
      ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ u hu) s a T) ≤
      Real.exp (β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ v hv) s a T) := by
  let G:=fun σ : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)=>
    F ((terminalSampleEquiv (S:=Configuration (n+1)) T).symm σ)
  have he (w:ℝ)(hw:w∈Icc (0:ℝ) 1):
      followupCavityPhysicalExpectation n β ρ hβ hρ s a T G w=
      ∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ w hw) s a T := by
    rw [followupCavityPhysicalExpectation_eq_actual n β ρ hβ hρ s a hq T G w hw,
      ←anisotropicFiniteRecordedTreeLaw_spin_marginal]
    have hG:Measurable G := (measurable_of_finite F).comp (terminalSampleEquiv (S:=Configuration (n+1)) T).symm.measurable
    rw [integral_map (φ:=fun z : CavityPathRecordSpace T (n+1)=>spins T z.2)
      ((measurable_spins T).comp measurable_snd).aemeasurable hG.aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall fun z=>by
      dsimp only [G]
      rw [←terminalSampleEquiv_recordSpins,(terminalSampleEquiv (S:=Configuration (n+1)) T).symm_apply_apply]
  rw [←he u hu,←he v hv]
  exact followupCavityPhysicalExpectation_comparison hn β ρ hβ hρ s a ha has hq T G (fun σ=>hF0 _) u v hu hv

theorem cavityNative_grid_positive_spin_comparison
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (μ:Paper.ParisiMeasure)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(hfloor:a≤Paper.parisiCDF μ 0)
    (q:ℕ→Paper.Overlap)(hq:Antitone q)(J:ℕ)(hJ:0<J)
    (hzero:(q 0:ℝ)=1)(htop:(q J:ℝ)=0)(T:FiniteTerminalGenealogy J)
    (F:TerminalSpins (Configuration (n+1)) T→ℝ)(hF0:∀σ,0≤F σ)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) 1)(hv:v∈Icc (0:ℝ) 1)(N:ℕ):
    (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
      ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
        (Paper.parisiGridMeasure μ N) a q T:Measure (CavityPathRecordSpace T (n+1)))) ≤
      Real.exp (β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ v hv)
          (Paper.parisiGridMeasure μ N) a q T:Measure (CavityPathRecordSpace T (n+1)))) := by
  let s:=Paper.parisiGridRSBScheme μ N
  have hs:s.q 1=0:=Paper.parisiGridSchemeOverlap_one N
  have hm:Paper.parisiSchemeMeasure s=Paper.parisiGridMeasure μ N:=FRSB.parisiSchemeMeasure_grid_eq μ N
  have hf:a≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) 0:=by
    rw [hm,←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass,zeroMass_eq_parisiCDF_zero]
    exact hfloor
  obtain ⟨K,r,e,hr,hrzero,har,he,hezero,hetop,hlevels⟩:=
    exists_same_measure_floor_observation_scheme_embedding s hs a hf q hq J hJ hzero htop
  let d:=observationEmbeddingGaps e
  have hdepth:observationRefinementDepth d J=K+2:=(observationRefinementDepth_embedding e he hezero J).trans hetop
  have hl(j:ℕ):anisotropicRecordedSchemeSchedule r (observationRefinementDepth d j)=q j:=by
    rw [observationRefinementDepth_embedding e he hezero]
    exact hlevels j
  let G:=fun σ : TerminalSpins (Configuration (n+1))
      (observationTreeDepthCast hdepth (observationRefineTree d T))=>F (observationRefinementTerminalProject d T hdepth σ)
  have heq (w:ℝ)(hw:w∈Icc (0:ℝ) 1):
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ w hw)
          (Paper.parisiGridMeasure μ N) a q T:Measure (CavityPathRecordSpace T (n+1))))=
      ∫z,G (finiteCascadeRecordTerminalSpins _ z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ w hw) r a
          (observationTreeDepthCast hdepth (observationRefineTree d T)) := by
    have hmap:=anisotropicRecordedProfileTreeLaw_refined_scheme
      (followupCavitySpinModel n β ρ hβ hρ w hw) r a q d hl T hdepth
    rw [hr,hm] at hmap
    change _=(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ w hw)
      (Paper.parisiGridMeasure μ N) a q T:Measure (CavityPathRecordSpace T (n+1))) at hmap
    rw [←hmap]
    have hF:Measurable (fun z : FiniteStateField (Configuration (n+1))×
        Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T=>
        F (finiteCascadeRecordTerminalSpins T z.2)):=
      (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
    rw [integral_map (measurable_id.prodMap (measurable_observationRefinementDepthProject d T hdepth)).aemeasurable hF.aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall fun z=>congrArg F (observationRefinementTerminalProject_record d T hdepth z.2).symm
  rw [heq u hu,heq v hv]
  have hh:=cavityFiniteRecorded_positive_spin_comparison hn β ρ hβ hρ r a ha har hrzero
    (observationTreeDepthCast hdepth (observationRefineTree d T)) G (fun σ=>hF0 _) u v hu hv
  simpa only [leafCount_observationRefinementDepthCast] using hh

theorem cavityNative_positive_spin_comparison
    (hn:0<n)(β ρ:ℝ)(hβ:0<β)(hρ:ρ∈Ioc (0:ℝ) 1)
    (μ:Paper.ParisiMeasure)(a:ℝ)(ha:a∈Icc (0:ℝ) 1)(hfloor:a≤Paper.parisiCDF μ 0)
    (q:ℕ→Paper.Overlap)(hq:Antitone q)(J:ℕ)(hJ:0<J)
    (hzero:(q 0:ℝ)=1)(htop:(q J:ℝ)=0)(T:FiniteTerminalGenealogy J)
    (F:TerminalSpins (Configuration (n+1)) T→ℝ)(hF0:∀σ,0≤F σ)
    (u v:ℝ)(hu:u∈Icc (0:ℝ) 1)(hv:v∈Icc (0:ℝ) 1):
    (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
      ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ u hu) μ a q T:Measure (CavityPathRecordSpace T (n+1)))) ≤
      Real.exp (β^2*(4*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2+
        2*(FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)+1))*
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ v hv) μ a q T:Measure (CavityPathRecordSpace T (n+1)))) := by
  let B:ℝ:=∑σ:TerminalSpins (Configuration (n+1)) T,‖F σ‖
  have hb(σ:TerminalSpins (Configuration (n+1)) T):‖F σ‖≤B:=
    Finset.single_le_sum (fun σ _=>norm_nonneg (F σ)) (Finset.mem_univ σ)
  have hFC:Continuous F:=continuous_of_discreteTopology
  let G : (FiniteStateField (Configuration (n+1))×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T)→ᵇℝ:=
    BoundedContinuousFunction.mkOfBound
      ⟨fun z=>F (finiteCascadeRecordTerminalSpins T z.2),
        hFC.comp ((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_snd)⟩
      (2*B) (fun z w=>(dist_le_norm_add_norm _ _).trans
        ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
  have ht(w:ℝ)(hw:w∈Icc (0:ℝ) 1):=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_anisotropicRecordedEnergyProbability_grid (followupCavitySpinModel n β ρ hβ hρ w hw) μ a q T hq) G
  exact le_of_tendsto_of_tendsto (ht u hu) ((ht v hv).const_mul _) (.of_forall fun N=>
    cavityNative_grid_positive_spin_comparison hn β ρ hβ hρ μ a ha hfloor q hq J hJ hzero htop T F hF0 u v hu hv N)

end QuantitativeFollowup
