module
public import QuantitativeFollowup.FollowupCavityCommonObservationTests
public import QuantitativeFollowup.FollowupCavityIndependentProductSecondResponseMultiplier
public import QuantitativeFollowup.FollowupCavityNativeCppSinglePairJets

@[expose] public section

/-! Independent first-response products pass on one genuine common profile.
The two observation trees retain their separate branch budgets. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n k J : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityPhysical_firstWithinJet_product_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (s : RSBScheme k) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (has : a ≤ s.m 1) (hq : s.q 1=0)
    (T U : FiniteTerminalGenealogy (k+2))
    (F : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy T)→ℝ)
    (hF : ∀r,|followupCavityPhysicalRecordObservable n T F r|≤1)
    (G : FiniteCascadeGenealogy.Samples (Configuration (n+1)) (asGenealogy U)→ℝ)
    (i l : ObservationLeaf (trimRoot U))
    (hG : ∀r,|followupCavityPhysicalRecordObservable n U G r|≤
      |cavityRecordedLeafPairDefect s (trimRoot U) i l r.2|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityPhysicalExpectation n β ρ hβ hρ s a T F) (Icc 0 1) 1 u*
      withinJet (followupCavityPhysicalExpectation n β ρ hβ hρ s a U G) (Icc 0 1) 1 u|≤
      (followupCavityAlpha n β ρ/2)^2*1800*
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiSchemeMeasure s) a+
          finiteCascadeUnweightedBranchSum
            (fun j=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s j)) (trimRoot T)+
          finiteCascadeUnweightedBranchSum
            (fun j=>cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s j)) (trimRoot U)) := by
  dsimp only
  have hα : 0≤followupCavityAlpha n β ρ/2:=
    div_nonneg (followupCavityAlpha_nonneg n β ρ hρ.2) (by norm_num)
  have hf:=(hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq T F u hu).derivWithin (uniqueDiffOn_Icc_zero_one u hu)
  have hg:=(hasDerivWithinAt_followupCavityPhysicalExpectation_six_terms_closed hn β ρ hβ hρ
    s a ha has hq U G u hu).derivWithin (uniqueDiffOn_Icc_zero_one u hu)
  have hh:=cavityIndependent_six_bounded_six_onePair_cubic_le hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) s a ha has hq T U
    (followupCavityPhysicalRecordObservable n T F) (measurable_followupCavityPhysicalRecordObservable T F) hF
    i l (followupCavityPhysicalRecordObservable n U G) (measurable_followupCavityPhysicalRecordObservable U G) hG
  have hmul (x y : ℝ) : (followupCavityAlpha n β ρ/2*x)*(followupCavityAlpha n β ρ/2*y)=
      (followupCavityAlpha n β ρ/2)^2*(x*y) := by ring
  simp only [withinJet]
  rw [hf,hg,hmul,
    abs_mul,abs_of_nonneg (sq_nonneg _)]
  exact (mul_le_mul_of_nonneg_left hh (sq_nonneg _)).trans_eq (by ring)

theorem cavityNativeGrid_firstWithinJet_product_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T U : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (hF : ∀σ,|F σ|≤1)
    (G : TerminalSpins (Configuration (n+1)) U→ℝ) (i l : ObservationLeaf U)
    (hG : ∀σ,|G σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel U i l))
      (observationLeafTerminalSpin U i σ) (observationLeafTerminalSpin U l σ)|)
    (N : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F)
        (Icc 0 1) 1 u*
      withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q U G)
        (Icc 0 1) 1 u|≤
      (followupCavityAlpha n β ρ/2)^2*1800*
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2*
        (cavityThirdMoment D (Paper.parisiGridMeasure μ N) a+
          finiteCascadeUnweightedBranchSum (fun j=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q j)) T+
          finiteCascadeUnweightedBranchSum (fun j=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q j)) U) := by
  dsimp only
  obtain ⟨K,s,d,hdepth,hμ,hszero,has,hl⟩:=
    exists_finite_floor_observation_geometry μ a hfloor q hq hJ hzero htop N
  let V:=observationTreeDepthCast hdepth (observationRefineTree d T)
  let W:=observationTreeDepthCast hdepth (observationRefineTree d U)
  let FT:=cavityObservationRefinedTerminalTest n d T hdepth F
  let GT:=cavityObservationRefinedTerminalTest n d U hdepth G
  have hfEq : Set.EqOn (followupCavityPhysicalExpectation n β ρ hβ hρ s a V FT)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F)
      (Icc (0:ℝ) 1) := by
    intro v hv
    rw [←hμ]
    exact cavityObservationRefinedTerminalTest_expectation β ρ hβ hρ s a hszero q d hl T hdepth F v hv
  have hgEq : Set.EqOn (followupCavityPhysicalExpectation n β ρ hβ hρ s a W GT)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q U G)
      (Icc (0:ℝ) 1) := by
    intro v hv
    rw [←hμ]
    exact cavityObservationRefinedTerminalTest_expectation β ρ hβ hρ s a hszero q d hl U hdepth G v hv
  have hh:=cavityPhysical_firstWithinJet_product_cubic_le hn β ρ hβ hρ s a ha has hszero V W FT
    (cavityObservationRefinedPhysicalTest_abs_le d T hdepth F 1 hF) GT
    (cavityObservationRefinedLeaf d U hdepth i) (cavityObservationRefinedLeaf d U hdepth l)
    (cavityObservationRefinedPhysicalTest_onePair_domination s hszero q d hl U hdepth G i l hG) u hu
  dsimp only at hh
  rw [cavityWithinJet_congr_eqOn hfEq 1 hu,cavityWithinJet_congr_eqOn hgEq 1 hu,hμ] at hh
  dsimp only [V,W] at hh
  rw [leafCount_observationRefinementDepthCast,leafCount_observationRefinementDepthCast,
    cavityObservationRefined_branchSum s hszero d T hdepth q hl,
    cavityObservationRefined_branchSum s hszero d U hdepth q hl] at hh
  exact hh

theorem cavityNative_firstWithinJet_product_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T U : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (hF : ∀σ,|F σ|≤1)
    (G : TerminalSpins (Configuration (n+1)) U→ℝ) (i l : ObservationLeaf U)
    (hG : ∀σ,|G σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel U i l))
      (observationLeafTerminalSpin U i σ) (observationLeafTerminalSpin U l σ)|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F) (Icc 0 1) 1 u*
      withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q U G) (Icc 0 1) 1 u|≤
      (followupCavityAlpha n β ρ/2)^2*1800*
        (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
        (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2*
        (cavityThirdMoment D μ a+
          finiteCascadeUnweightedBranchSum (fun j=>cavityCubicPairMoment D μ a (q j)) T+
          finiteCascadeUnweightedBranchSum (fun j=>cavityCubicPairMoment D μ a (q j)) U) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  have hf:=(followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F).1 1 |>.tendsto_at hu
  have hg:=(followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop U G).1 1 |>.tendsto_at hu
  have hfloor' : μ∈scalarFloor a:=by rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero];exact hfloor
  have hgrid:=FRSB.tendsto_parisiGridMeasure μ
  have hM:=tendsto_cavityThirdMoment_of_weak D (fun N=>Paper.parisiGridMeasure μ N) μ a ha
    (fun N=>parisiGridMeasure_mem_scalarFloor μ a hfloor' N) hfloor' hgrid
  have hχ (j : ℕ):Tendsto (fun N=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q j))
      atTop (𝓝 (cavityCubicPairMoment D μ a (q j))) := by
    have hh:=((continuous_cavityCubicPairMoment_profile D a).tendsto (μ,q j)).comp
      (hgrid.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def] using hh
  have hBT:=tendsto_finiteCascadeUnweightedBranchSum atTop _ _ hχ T
  have hBU:=tendsto_finiteCascadeUnweightedBranchSum atTop _ _ hχ U
  exact le_of_tendsto_of_tendsto (hf.mul hg |>.abs)
    ((hM.add hBT |>.add hBU).const_mul ((followupCavityAlpha n β ρ/2)^2*1800*
      (FiniteCascadeGenealogy.leafCount (asGenealogy T):ℝ)^2*
      (FiniteCascadeGenealogy.leafCount (asGenealogy U):ℝ)^2))
    (.of_forall fun N=>cavityNativeGrid_firstWithinJet_product_cubic_le hn β ρ hβ hρ μ a ha hfloor
      q hq hJ hzero htop T U F hF G i l hG N u hu)

private theorem cppCrossSchedule_antitone (p : Paper.Overlap) :
    Antitone (anisotropicBinaryObservationSchedule p) := by
  apply antitone_nat_of_succ_le
  intro j
  rcases j with _|_|j
  · exact p.property.2
  · exact p.property.1
  · exact le_rfl

private theorem cppCrossTau_domination (p : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree) :
    |cavityCppTauTerminalTest n p σ|≤
      |cavitySpinOverlapDefect n
        (anisotropicBinaryObservationSchedule p
          (observationCommonLevel anisotropicBinaryObservationTree (Sum.inl ()) (Sum.inr ())))
        (observationLeafTerminalSpin anisotropicBinaryObservationTree (Sum.inl ()) σ)
        (observationLeafTerminalSpin anisotropicBinaryObservationTree (Sum.inr ()) σ)| := by
  change |cavityRestOverlap n σ.1 σ.2-(p:ℝ)|≤|cavitySpinOverlapDefect n p σ.1 σ.2|
  exact (cavitySpinOverlapDefect_abs_eq_rest n p σ.1 σ.2).ge

theorem abs_followupCavityCppCrossFirst_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (p : Paper.Overlap) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppEpsilonTerminalTest n)) (Icc 0 1) 1 u*
      withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a
        (anisotropicBinaryObservationSchedule p) anisotropicBinaryObservationTree
        (cavityCppTauTerminalTest n p)) (Icc 0 1) 1 u|≤
      (followupCavityAlpha n β ρ/2)^2*28800*
        (cavityThirdMoment D μ a+2*cavityCubicPairMoment D μ a p) := by
  have hh:=cavityNative_firstWithinJet_product_cubic_le hn β ρ hβ hρ μ a ha hfloor
    (anisotropicBinaryObservationSchedule p) (cppCrossSchedule_antitone p) (by norm_num) rfl rfl
    anisotropicBinaryObservationTree anisotropicBinaryObservationTree (cavityCppEpsilonTerminalTest n)
    cavityCppEpsilonTerminalTest_abs_le (cavityCppTauTerminalTest n p) (Sum.inl ()) (Sum.inr ())
    (cppCrossTau_domination p) u hu
  convert! hh using 1 <;>
    simp only [anisotropicBinaryObservationTree,asGenealogy,FiniteCascadeGenealogy.leafCount,
      finiteCascadeUnweightedBranchSum,anisotropicBinaryObservationSchedule] <;> norm_num <;> ring

end QuantitativeFollowup
