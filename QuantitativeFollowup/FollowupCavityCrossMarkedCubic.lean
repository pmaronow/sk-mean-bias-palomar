module
public import QuantitativeFollowup.FollowupCavitySingleMarkedCubic
public import QuantitativeFollowup.FollowupCavityLinearCrossGraftLaw
public import QuantitativeFollowup.FollowupCavityCrossGraftCubicBudget

@[expose] public section

/-! The literal cross/current conditional mark products are cubic
products of genuine descendants of the enlarged physical tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityCrossVertex_leaf_triple_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v w : FiniteCascadeRecordVertex (trimRoot T)) (i l : Fin 2 → ObservationLeaf (trimRoot T)) :
    (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z.1 *
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) z.2.1 z.2.2|
        ∂anisotropicCrossVertexMarkedLaw D s a T v w) ≤
      finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) +
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s v.depth) +
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s w.depth) := by
  let e := finiteCascadeCrossContinuationExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1))
    observationLinearTree (fun d => observationLinearSpin d) v w
  let φ := fun z : FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (finiteCascadeCrossContinuationGraft observationLinearTree v w) =>
    ((z.1,(e z.2).1),(e z.2).2)
  let G := fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) ×
      (Configuration (n+1) × Configuration (n+1)) =>
    |cavityRecordedPairProduct s (trimRoot T) i l z.1 *
      cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) z.2.1 z.2.2|
  have he := measurable_finiteCascadeCrossContinuationExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1))
    observationLinearTree (fun d => observationLinearSpin d) (fun d => measurable_observationLinearSpin d) v w
  have hφ : Measurable φ := (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hpair : Measurable (fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) ×
      (Configuration (n+1) × Configuration (n+1)) => z.2) := measurable_snd
  have hG : Measurable G :=
    ((measurable_cavityRecordedPairProduct (n:=n) s (trimRoot T) i l).comp measurable_fst |>.mul
      ((measurable_of_finite (fun z : Configuration (n+1) × Configuration (n+1) =>
        cavitySpinOverlapDefect n (cavityPhysicalCommonOverlap s (trimRoot T) v w) z.1 z.2)).comp hpair)).abs
  have hm : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w))).map φ = anisotropicCrossVertexMarkedLaw D s a T v w :=
    anisotropicCrossVertexMarkedLaw_eq_linear_graft D s a T v w
  have hmap := integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w))) hφ.aemeasurable hG.aestronglyMeasurable
  rw [hm] at hmap
  let ii : Fin 3 → ObservationLeaf (finiteCascadeCrossContinuationGraft observationLinearTree v w) := ![finiteCascadeLinearCrossOldLeaf v w (i 0),
    finiteCascadeLinearCrossOldLeaf v w (i 1),finiteCascadeLinearCrossFirstLeaf v w]
  let ll : Fin 3 → ObservationLeaf (finiteCascadeCrossContinuationGraft observationLinearTree v w) := ![finiteCascadeLinearCrossOldLeaf v w (l 0),
    finiteCascadeLinearCrossOldLeaf v w (l 1),finiteCascadeLinearCrossSecondLeaf v w]
  have hlevel : (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) v w) : ℝ)=
      cavityPhysicalCommonOverlap s (trimRoot T) v w := by
    rw [cavityProfileLevel,scalarSchemeTransportNode_coe s _ (by omega)]
    rfl
  have hi : (∫z,G (φ z) ∂anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w))) =
      cavityTrimmedRecordedTripleDefectMoment D s a (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w)) ii ll := by
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp [G,φ,e,cavityRecordedPairProduct,cavityTrimmedRecordedTripleDefectMoment,ii,ll]
      simp only [cavityRecordedLeafPairDefect,finiteCascadeLinearCrossOldLeaf_commonLevel,
        finiteCascadeLinearCrossFresh_commonLevel,finiteCascadeLinearCrossOldLeaf_spin,
        finiteCascadeLinearCrossFirstLeaf_spin,finiteCascadeLinearCrossSecondLeaf_spin,hlevel]
  rw [hmap,hi]
  have hbound := cavityTrimmedRecordedTripleDefectMoment_le_branch hn D s a hq (.advance (finiteCascadeCrossContinuationGraft observationLinearTree v w)) ii ll
  simpa only [trimRoot,finiteCascadeLinearCross_branchSum] using hbound

end QuantitativeFollowup
