module
public import QuantitativeFollowup.FollowupCavityCommonObservationTests
public import QuantitativeFollowup.FollowupCavityCppPairLaw
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseBound
public import QuantitativeFollowup.FollowupCavityNativeCppSinglePairJets

@[expose] public section

/-! The bounded epsilon second response multiplies an independently sampled
actual rest-pair expectation. Its external cube is the literal local moment. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n : ℕ}
set_option maxHeartbeats 2600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem cppExternalSchedule_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro j
  rcases j with _|_|j
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

theorem abs_followupCavityCppEpsilonSecondTau_grid_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) (N : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppEpsilonTerminalTest n)) (Icc 0 1) 2 u*
      followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppTauTerminalTest n p) u|≤
      (followupCavityAlpha n β ρ/2)^2*cavityIndependentSecondStreamingCost 2*
        (cavityThirdMoment D (Paper.parisiGridMeasure μ N) a+
          2*cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a p) := by
  dsimp only
  let q:=anisotropicBinaryObservationSchedule p
  obtain ⟨K,s,d,hdepth,hμ,hszero,has,hl⟩:=exists_finite_floor_observation_geometry (J:=2) μ a hfloor q
    (cppExternalSchedule_antitone p) (by norm_num) rfl rfl N
  let T:=anisotropicBinaryObservationTree
  let U:=observationTreeDepthCast hdepth (observationRefineTree d T)
  let F:=cavityObservationRefinedTerminalTest n d T hdepth (cavityCppEpsilonTerminalTest n)
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  let Q : Measure (Configuration (n+1)×Configuration (n+1)):=
    (anisotropicBinarySpinProbability D (Paper.parisiSchemeMeasure s) a p : Measure _)
  haveI : IsProbabilityMeasure Q := by dsimp only [Q];infer_instance
  have hF : ∀r,|followupCavityPhysicalRecordObservable n U F r|≤1:=
    cavityObservationRefinedPhysicalTest_abs_le d T hdepth (cavityCppEpsilonTerminalTest n)
      1 cavityCppEpsilonTerminalTest_abs_le
  have hEq : Set.EqOn (followupCavityPhysicalExpectation n β ρ hβ hρ s a U F)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T
        (cavityCppEpsilonTerminalTest n)) (Icc (0:ℝ) 1) := by
    intro v hv
    rw [←hμ]
    exact cavityObservationRefinedTerminalTest_expectation β ρ hβ hρ s a hszero q d hl T hdepth
      (cavityCppEpsilonTerminalTest n) v hv
  have hh:=abs_followupCavityPhysicalExpectation_secondWithinJet_external_cubic_le hn β ρ hβ hρ
    s a ha has hszero U F hF Q (cavityCppTauTerminalTest n p) (measurable_of_finite _)
    (cavityCppTauTerminalTest_abs_le p) u hu
  change |withinJet (followupCavityPhysicalExpectation n β ρ hβ hρ s a U F) (Icc 0 1) 2 u*
    (∫σ,cavityCppTauTerminalTest n p σ∂Q)|≤_ at hh
  dsimp only [Q,D] at hh
  rw [cavityWithinJet_congr_eqOn hEq 2 hu,
    integral_cavityCppTauTerminalTest_abs_cube_eq,
    ←followupCavityCppBinary_expectation_eq_integral β ρ hβ hρ (Paper.parisiSchemeMeasure s) a p
      (cavityCppTauTerminalTest n p) u hu,hμ] at hh
  dsimp only [U] at hh
  rw [leafCount_observationRefinementDepthCast,
    cavityObservationRefined_branchSum s hszero d T hdepth q hl] at hh
  convert! hh using 1 <;>
    simp only [T,q,anisotropicBinaryObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount,
      finiteCascadeUnweightedBranchSum,anisotropicBinaryObservationSchedule] <;> norm_num <;> ring <;> simp

theorem abs_followupCavityCppEpsilonSecondTau_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppEpsilonTerminalTest n)) (Icc 0 1) 2 u*
      followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppTauTerminalTest n p) u|≤
      (followupCavityAlpha n β ρ/2)^2*cavityIndependentSecondStreamingCost 2*
        (cavityThirdMoment D μ a+2*cavityCubicPairMoment D μ a p) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  have he:=(followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (cppExternalSchedule_antitone p) (by norm_num) rfl rfl
    anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)).1 2 |>.tendsto_at hu
  have ht:=tendsto_followupCavityNativeTerminalExpectation_grid β ρ hβ hρ μ a
    (anisotropicBinaryObservationSchedule p) (cppExternalSchedule_antitone p)
    anisotropicBinaryObservationTree (cavityCppTauTerminalTest n p) u
  have hfloor' : μ∈scalarFloor a:=by rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero];exact hfloor
  have hgrid:=FRSB.tendsto_parisiGridMeasure μ
  have hM:=tendsto_cavityThirdMoment_of_weak D (fun N=>Paper.parisiGridMeasure μ N) μ a ha
    (fun N=>parisiGridMeasure_mem_scalarFloor μ a hfloor' N) hfloor' hgrid
  have hχ:Tendsto (fun N=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a p)
      atTop (𝓝 (cavityCubicPairMoment D μ a p)) := by
    have hh:=((continuous_cavityCubicPairMoment_profile D a).tendsto (μ,p)).comp
      (hgrid.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def] using hh
  exact le_of_tendsto_of_tendsto (he.mul ht |>.abs)
    ((hM.add (hχ.const_mul 2)).const_mul ((followupCavityAlpha n β ρ/2)^2*cavityIndependentSecondStreamingCost 2))
    (.of_forall fun N=>abs_followupCavityCppEpsilonSecondTau_grid_cubic_le hn β ρ hβ hρ μ a ha hfloor p N u hu)

end QuantitativeFollowup
