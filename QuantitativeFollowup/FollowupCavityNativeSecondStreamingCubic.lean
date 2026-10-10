module
public import QuantitativeFollowup.FollowupCavityObservationPairRealization
public import QuantitativeFollowup.FollowupCavityNativeStreamingRegularity
public import QuantitativeFollowup.FollowupCavitySecondStreamingCubic
public import QuantitativeFollowup.FollowupCavityNativePairIncrement

@[expose] public section

/-! The true finite cubic second-jet estimate passes to the actual native
expectation. Exact refinement preserves old pairs and all branch budgets. -/
noncomputable section
open Set Filter
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
open FourPapersCommon.FiniteStreamingPolynomials
variable {n J : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem abs_followupCavityNativeGrid_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (i l : ObservationLeaf T)
    (hdom : ∀σ,|F σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel T i l))
      (observationLeafTerminalSpin T i σ) (observationLeafTerminalSpin T l σ)|)
    (N : ℕ) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ
      (Paper.parisiGridMeasure μ N) a q T F) (Icc (0:ℝ) 1) 2 u|≤
      (followupCavityAlpha n β ρ/2)^2*
        cavitySecondStreamingCost (FiniteCascadeGenealogy.leafCount (asGenealogy T))*
        (cavityThirdMoment D (Paper.parisiGridMeasure μ N) a+
          finiteCascadeUnweightedBranchSum
            (fun d=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q d)) T) := by
  dsimp only
  have hF (σ):|F σ|≤2:=(hdom σ).trans (cavitySpinOverlapDefect_abs_le_two n _
    (q (observationCommonLevel T i l)).property _ _)
  obtain ⟨K,s,A,i',l',hμ,hszero,has,hcomp,hbound,he,hpair,hbudget⟩:=
    exists_finite_cavityStreamingAtom_grid_pair_representation β ρ hβ hρ μ a hfloor
      q hq hJ hzero htop T F 2 (by norm_num) hF i l hdom N
  have hEq : Set.EqOn (A.eval β ρ hβ hρ s a)
      (followupCavityNativeTerminalExpectation n β ρ hβ hρ (Paper.parisiGridMeasure μ N) a q T F)
      (Icc (0:ℝ) 1):=fun v hv=>he v hv
  have hh:=abs_followupCavityPhysicalExpectation_secondWithinJet_cubic_le hn β ρ hβ hρ s a ha has hszero
    A.tree A.test i' l' hpair u hu
  change |withinJet (A.eval β ρ hβ hρ s a) (Icc (0:ℝ) 1) 2 u|≤_ at hh
  change FiniteCascadeGenealogy.leafCount (asGenealogy A.tree)=_ at hcomp
  rw [cavityWithinJet_congr_eqOn hEq 2 hu,hμ,hcomp,
    hbudget (cavityCubicPairMoment (followupCavitySpinModel n β ρ hβ hρ u hu)
      (Paper.parisiGridMeasure μ N) a)] at hh
  exact hh

theorem abs_followupCavityNativeTerminalExpectation_secondWithinJet_cubic_le
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : a ≤ Paper.parisiCDF μ 0)
    (q : ℕ→Paper.Overlap) (hq : Antitone q) (hJ : 0<J)
    (hzero : (q 0:ℝ)=1) (htop : (q J:ℝ)=0) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (i l : ObservationLeaf T)
    (hdom : ∀σ,|F σ|≤|cavitySpinOverlapDefect n (q (observationCommonLevel T i l))
      (observationLeafTerminalSpin T i σ) (observationLeafTerminalSpin T l σ)|)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    let D:=followupCavitySpinModel n β ρ hβ hρ u hu
    |withinJet (followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a q T F)
      (Icc (0:ℝ) 1) 2 u|≤
      (followupCavityAlpha n β ρ/2)^2*
        cavitySecondStreamingCost (FiniteCascadeGenealogy.leafCount (asGenealogy T))*
        (cavityThirdMoment D μ a+
          finiteCascadeUnweightedBranchSum (fun d=>cavityCubicPairMoment D μ a (q d)) T) := by
  dsimp only
  let D:=followupCavitySpinModel n β ρ hβ hρ u hu
  have hj:=(followupCavityNativeTerminalExpectation_jet_limit hn β ρ hβ hρ μ a ha hfloor
    q hq hJ hzero htop T F).1 2 |>.tendsto_at hu
  have hμ : μ∈scalarFloor a:=by rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero];exact hfloor
  have hgrid:=FRSB.tendsto_parisiGridMeasure μ
  have hM:=tendsto_cavityThirdMoment_of_weak D (fun N=>Paper.parisiGridMeasure μ N) μ a ha
    (fun N=>parisiGridMeasure_mem_scalarFloor μ a hμ N) hμ hgrid
  have hχ (d : ℕ) : Tendsto (fun N=>cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q d))
      atTop (𝓝 (cavityCubicPairMoment D μ a (q d))) := by
    have hh:=((continuous_cavityCubicPairMoment_profile D a).tendsto (μ,q d)).comp
      (hgrid.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def] using hh
  have hB:=tendsto_finiteCascadeUnweightedBranchSum atTop _ _ hχ T
  have hR:=(hM.add hB).const_mul ((followupCavityAlpha n β ρ/2)^2*
    cavitySecondStreamingCost (FiniteCascadeGenealogy.leafCount (asGenealogy T)))
  exact le_of_tendsto_of_tendsto hj.abs hR (.of_forall fun N=>
    abs_followupCavityNativeGrid_secondWithinJet_cubic_le hn β ρ hβ hρ μ a ha hfloor
      q hq hJ hzero htop T F i l hdom N u hu)

end QuantitativeFollowup
