module
public import QuantitativeFollowup.FollowupCavityTerminalPairIncrement
public import FourPapersCommon.FiniteObservationRefinementTerminalLeaves
public import QuantitativeFollowup.FollowupCavityCubicProfileContinuity

@[expose] public section

/-! Genuine endpoint increments of terminal two-pair tests under the
native observation genealogy. Exact observation refinement preserves
the root floor, the four chosen marks and the inherited branch budget. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityObservationTerminalPairProduct (q : ℕ → Paper.Overlap) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (i l : Fin 2 → ObservationLeaf T)
    (σ : TerminalSpins (Configuration (n+1)) T) : ℝ :=
  cavitySpinOverlapDefect n (q (observationCommonLevel T (i 0) (l 0)))
    (observationTerminalSpin T (i 0) σ) (observationTerminalSpin T (l 0) σ)*
  cavitySpinOverlapDefect n (q (observationCommonLevel T (i 1) (l 1)))
    (observationTerminalSpin T (i 1) σ) (observationTerminalSpin T (l 1) σ)

theorem cavityNative_grid_terminalPair_sub_le
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (J : ℕ) (hJ : 0<J)
    (hzero : (q 0 : ℝ)=1) (htop : (q J : ℝ)=0) (T : FiniteTerminalGenealogy J)
    (i l : Fin 2 → ObservationLeaf T) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (hdom : ∀σ, |F σ|≤|cavityObservationTerminalPairProduct q T i l σ|)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (N : ℕ) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |(∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ y hy)
          (Paper.parisiGridMeasure μ N) a q T : Measure (CavityPathRecordSpace T (n+1))))-
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ x hx)
          (Paper.parisiGridMeasure μ N) a q T : Measure (CavityPathRecordSpace T (n+1))))| ≤
      (followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)^2)*
        Real.exp (21*β^2)*(cavityThirdMoment D (Paper.parisiGridMeasure μ N) a+
          finiteCascadeUnweightedBranchSum (fun d => cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q d)) T))*|y-x| := by
  dsimp only
  let s := Paper.parisiGridRSBScheme μ N
  have hs : s.q 1=0 := Paper.parisiGridSchemeOverlap_one N
  have hm : Paper.parisiSchemeMeasure s=Paper.parisiGridMeasure μ N := FRSB.parisiSchemeMeasure_grid_eq μ N
  have hf : a≤Paper.parisiCDF (Paper.parisiSchemeMeasure s) 0 := by
    rw [hm,←zeroMass_eq_parisiCDF_zero,parisiGridMeasure_root_mass,zeroMass_eq_parisiCDF_zero]
    exact hfloor
  obtain ⟨K,r,e,hr,hrzero,har,he,hezero,hetop,hlevels⟩ :=
    exists_same_measure_floor_observation_scheme_embedding s hs a hf q hq J hJ hzero htop
  let d := observationEmbeddingGaps e
  have hdepth : observationRefinementDepth d J=K+2 :=
    (observationRefinementDepth_embedding e he hezero J).trans hetop
  have hl (j : ℕ) : anisotropicRecordedSchemeSchedule r (observationRefinementDepth d j)=q j := by
    rw [observationRefinementDepth_embedding e he hezero]
    exact hlevels j
  have hl' (j : ℕ) : cavityProfileLevel r (observationRefinementDepth d j)=q j := by
    apply Subtype.ext
    rw [cavityProfileLevel_coe_for_streaming]
    have hh := congrArg (fun z : Paper.Overlap => (z : ℝ)) (hl j)
    simpa only [anisotropicRecordedSchemeSchedule,anisotropicFiniteMeshNode_coe r _ (Nat.sub_le _ _)] using hh
  let U := observationTreeDepthCast hdepth (observationRefineTree d T)
  let emb := observationRefinementDepthLeafEmbed d T hdepth
  let G : TerminalSpins (Configuration (n+1)) U → ℝ :=
    fun σ => F (observationRefinementTerminalProject d T hdepth σ)
  have hG (σ : TerminalSpins (Configuration (n+1)) U) :
      |G σ|≤|cavityTerminalPairProduct r U (emb ∘ i) (emb ∘ l) σ| := by
    have hh := hdom (observationRefinementTerminalProject d T hdepth σ)
    dsimp only [G]
    convert hh using 1
    simp only [cavityTerminalPairProduct,cavityObservationTerminalPairProduct,Function.comp_apply,emb,U,
      observationRefinementDepthLeafEmbed_commonLevel,hl',observationRefinementTerminalProject_leaf]
  have heq (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ w hw)
          (Paper.parisiGridMeasure μ N) a q T : Measure (CavityPathRecordSpace T (n+1))))=
      ∫z : CavityPathRecordSpace U (n+1),G (finiteCascadeRecordTerminalSpins U z.2)
        ∂anisotropicFiniteRecordedTreeLaw (followupCavitySpinModel n β ρ hβ hρ w hw) r a U := by
    have hmap := anisotropicRecordedProfileTreeLaw_refined_scheme
      (followupCavitySpinModel n β ρ hβ hρ w hw) r a q d hl T hdepth
    rw [hr,hm] at hmap
    change _=(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ w hw)
      (Paper.parisiGridMeasure μ N) a q T : Measure (CavityPathRecordSpace T (n+1))) at hmap
    rw [←hmap]
    have hF : Measurable (fun z : CavityPathRecordSpace T (n+1) =>
        F (finiteCascadeRecordTerminalSpins T z.2)) :=
      (measurable_of_finite F).comp ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)
    rw [integral_map (measurable_id.prodMap (measurable_observationRefinementDepthProject d T hdepth)).aemeasurable hF.aestronglyMeasurable]
    apply integral_congr_ae
    exact .of_forall fun z => congrArg F (observationRefinementTerminalProject_record d T hdepth z.2).symm
  rw [heq y hy,heq x hx]
  have hh := cavityFiniteRecorded_terminalPair_sub_le hn β ρ hβ hρ r a ha har hrzero U
    (emb ∘ i) (emb ∘ l) G hG v hv x y hx hy
  dsimp only at hh
  simp only [U,hr,hm,leafCount_observationRefinementDepthCast,
    finiteCascadeUnweightedBranchSum_observationRefinementDepth,hl'] at hh
  exact hh

theorem tendsto_finiteCascadeUnweightedBranchSum {α : Type*} (l : Filter α)
    (χ : α → ℕ → ℝ) (η : ℕ → ℝ) (hχ : ∀d, Tendsto (fun x => χ x d) l (𝓝 (η d)))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    Tendsto (fun x => finiteCascadeUnweightedBranchSum (χ x) T) l
      (𝓝 (finiteCascadeUnweightedBranchSum η T)) := by
  induction T with
  | leaf => exact tendsto_const_nhds
  | advance T ih => exact ih
  | @fork j T U ihT ihU => exact (ihT.add ihU).add (hχ j)

theorem cavityNative_terminalPair_sub_le
    (hn : 0 < n) (β ρ : ℝ) (hβ : 0 < β) (hρ : ρ ∈ Ioc (0 : ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hfloor : a≤Paper.parisiCDF μ 0)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (J : ℕ) (hJ : 0<J)
    (hzero : (q 0 : ℝ)=1) (htop : (q J : ℝ)=0) (T : FiniteTerminalGenealogy J)
    (i l : Fin 2 → ObservationLeaf T) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (hdom : ∀σ, |F σ|≤|cavityObservationTerminalPairProduct q T i l σ|)
    (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1)
    (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    let D := followupCavitySpinModel n β ρ hβ hρ v hv
    |(∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ y hy)
          μ a q T : Measure (CavityPathRecordSpace T (n+1))))-
      (∫z : CavityPathRecordSpace T (n+1),F (finiteCascadeRecordTerminalSpins T z.2)
        ∂(anisotropicRecordedEnergyProbability (followupCavitySpinModel n β ρ hβ hρ x hx)
          μ a q T : Measure (CavityPathRecordSpace T (n+1))))| ≤
      (followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)^2)*
        Real.exp (21*β^2)*(cavityThirdMoment D μ a+
          finiteCascadeUnweightedBranchSum (fun d => cavityCubicPairMoment D μ a (q d)) T))*|y-x| := by
  dsimp only
  let D := followupCavitySpinModel n β ρ hβ hρ v hv
  let B : ℝ := ∑σ : TerminalSpins (Configuration (n+1)) T, ‖F σ‖
  have hb (σ) : ‖F σ‖≤B := Finset.single_le_sum (fun σ _ => norm_nonneg (F σ)) (Finset.mem_univ σ)
  let G : CavityPathRecordSpace T (n+1) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun z => F (finiteCascadeRecordTerminalSpins T z.2),
      (continuous_of_discreteTopology (f:=F)).comp ((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_snd)⟩
    (2*B) (fun z w => (dist_le_norm_add_norm _ _).trans ((add_le_add (hb _) (hb _)).trans_eq (by ring)))
  have ht (w : ℝ) (hw : w ∈ Icc (0 : ℝ) 1) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
      (tendsto_anisotropicRecordedEnergyProbability_grid (followupCavitySpinModel n β ρ hβ hρ w hw) μ a q T hq) G
  have hμ : μ ∈ scalarFloor a := by rw [mem_scalarFloor_iff,zeroMass_eq_parisiCDF_zero]; exact hfloor
  have hgrid := FRSB.tendsto_parisiGridMeasure μ
  have hM := tendsto_cavityThirdMoment_of_weak D (fun N => Paper.parisiGridMeasure μ N) μ a ha
    (fun N => parisiGridMeasure_mem_scalarFloor μ a hμ N) hμ hgrid
  have hχ (d : ℕ) : Tendsto (fun N => cavityCubicPairMoment D (Paper.parisiGridMeasure μ N) a (q d))
      atTop (𝓝 (cavityCubicPairMoment D μ a (q d))) := by
    have hh := ((continuous_cavityCubicPairMoment_profile D a).tendsto (μ,q d)).comp
      (hgrid.prodMk_nhds tendsto_const_nhds)
    simpa only [Function.comp_def] using hh
  have hB := tendsto_finiteCascadeUnweightedBranchSum atTop _ _ hχ T
  have hR := (((hM.add hB).const_mul
    (followupCavityAlpha n β ρ/2*(15*(FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)^2)*Real.exp (21*β^2))).mul_const |y-x|)
  exact le_of_tendsto_of_tendsto (((ht y hy).sub (ht x hx)).abs) hR (.of_forall fun N =>
    cavityNative_grid_terminalPair_sub_le hn β ρ hβ hρ μ a ha hfloor q hq J hJ hzero htop T i l F hdom v hv x y hx hy N)

end QuantitativeFollowup
