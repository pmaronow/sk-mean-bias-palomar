module
public import QuantitativeFollowup.FollowupCavitySingleMarkedCubic
public import QuantitativeFollowup.FollowupCavityFutureVertexGraftLaw
public import QuantitativeFollowup.FollowupCavityFutureDepthLevels
public import QuantitativeFollowup.FollowupCavityFutureGraftCubicBudget

@[expose] public section

/-! The literal strict-future conditional pair is a genuine pair of
continuation leaves. Its physical split is exact at free-measure atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityFutureVertex_leaf_triple_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (q : Paper.Overlap) (hlevel : cavityProfileLevel s (cavityFiniteFutureDepth s v.depth q)=q) :
    (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n q z.2.1 z.2.2|
      ∂anisotropicFutureVertexMarkedLaw D s a T v q) ≤
      finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) +
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s v.depth) +
      cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a q := by
  let p := cavityFiniteFutureDepth s v.depth q
  have hlevelp : cavityProfileLevel s p=q := hlevel
  let A : (d : ℕ) → FiniteTerminalGenealogy d := fun d => (finiteCascadeFuturePairTree p d).tree
  let e := finiteCascadeFutureGraftExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1)) v p
  let φ := fun z : FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (finiteCascadeFutureVertexGraft v p) =>
    ((z.1,(e z.2).1),(e z.2).2)
  let G := fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) ×
      (Configuration (n+1) × Configuration (n+1)) =>
    |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n q z.2.1 z.2.2|
  have he := measurable_finiteCascadeFutureGraftExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1)) v p
  have hφ : Measurable φ := (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hpair : Measurable (fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) ×
      (Configuration (n+1) × Configuration (n+1)) => z.2) := measurable_snd
  have hG : Measurable G :=
    ((measurable_cavityRecordedPairProduct (n:=n) s (trimRoot T) i l).comp measurable_fst |>.mul
      ((measurable_of_finite (fun z : Configuration (n+1) × Configuration (n+1) =>
        cavitySpinOverlapDefect n q z.1 z.2)).comp hpair)).abs
  have hm : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeFutureVertexGraft v p))).map φ =
      anisotropicFutureVertexMarkedLaw D s a T v q :=
    anisotropicFutureVertexMarkedLaw_eq_graft D s a T v q
  have hmap := integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeFutureVertexGraft v p)))
    hφ.aemeasurable hG.aestronglyMeasurable
  rw [hm] at hmap
  let ii : Fin 3 → ObservationLeaf (finiteCascadeFutureVertexGraft v p) := ![
    finiteCascadeContinuationOldLeaf A v (i 0),finiteCascadeContinuationOldLeaf A v (i 1),
    finiteCascadeContinuationNewLeaf A v (observationPairFirstLeaf (finiteCascadeFuturePairTree p v.depth))]
  let ll : Fin 3 → ObservationLeaf (finiteCascadeFutureVertexGraft v p) := ![
    finiteCascadeContinuationOldLeaf A v (l 0),finiteCascadeContinuationOldLeaf A v (l 1),
    finiteCascadeContinuationNewLeaf A v (observationPairSecondLeaf (finiteCascadeFuturePairTree p v.depth))]
  have hsplit := finiteCascadeFuturePairTree_split p v.depth (cavityFiniteFutureDepth_le s v.depth q)
  have hi : (∫z,G (φ z) ∂anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeFutureVertexGraft v p))) =
      cavityTrimmedRecordedTripleDefectMoment D s a (.advance (finiteCascadeFutureVertexGraft v p)) ii ll := by
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp [G,φ,e,cavityRecordedPairProduct,cavityTrimmedRecordedTripleDefectMoment,ii,ll]
      simp only [trimRoot,finiteCascadeFutureVertexGraft,A,finiteCascadeFutureGraftExtract,finiteCascadeContinuationExtract_eq_records,
        observationPair_spins_eq_leaf_pair,cavityRecordedLeafPairDefect,
        finiteCascadeContinuationOldLeaf_commonLevel,finiteCascadeContinuationNewLeaf_commonLevel,
        finiteCascadeContinuationOldLeaf_spin,finiteCascadeContinuationNewLeaf_spin,
        observationPair_commonLevel,hsplit,hlevelp]
  rw [hmap,hi]
  have hbound := cavityTrimmedRecordedTripleDefectMoment_le_branch hn D s a hq
    (.advance (finiteCascadeFutureVertexGraft v p)) ii ll
  rw [trimRoot,finiteCascadeFutureVertexGraft_branchSum _ v p (cavityFiniteFutureDepth_le s v.depth q)] at hbound
  simpa only [p,hlevel] using hbound

end QuantitativeFollowup
