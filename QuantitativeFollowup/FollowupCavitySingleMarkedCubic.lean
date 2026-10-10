module
public import QuantitativeFollowup.FollowupCavityTrimmedCubic
public import QuantitativeFollowup.FollowupCavityLinearVertexGraftLaw
public import FourPapersCommon.FiniteCascadeContinuationLeafGeometry

@[expose] public section

/-! The original/fresh cubic integrand is dominated under its literal
conditional mark law by the branch budget of its actual enlarged tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper SpinGlass.Targets FiniteTerminalGenealogy
variable {n k : ℕ}
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem linearLeaf_spin {E S : Type} (d : ℕ) (z : Records E S (observationLinearTree d)) :
    observationLeafSpin (observationLinearTree d) (observationLinearLeaf d) z=observationLinearSpin d z := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih z.2

def cavityRecordedPairProduct (s : RSBScheme k) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i l : Fin 2 → ObservationLeaf T)
    (r : FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T) : ℝ :=
  cavityRecordedLeafPairDefect s T (i 0) (l 0) r.2 * cavityRecordedLeafPairDefect s T (i 1) (l 1) r.2

theorem measurable_cavityRecordedPairProduct (s : RSBScheme k) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (i l : Fin 2 → ObservationLeaf T) : Measurable (cavityRecordedPairProduct (n:=n) s T i l) := by
  have hp (m : Fin 2) : Measurable (fun r : FiniteStateField (Configuration (n+1)) ×
      Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) T =>
      cavityRecordedLeafPairDefect (n:=n) s T (i m) (l m) r.2) :=
    (measurable_cavityRecordedLeafPairDefect (n:=n) (E:=FiniteStateField (Configuration (n+1))) s T (i m) (l m)).comp measurable_snd
  exact (hp 0).mul (hp 1)

theorem cavityRecordedLeafPairDefect_continuation_old {j : ℕ} (s : RSBScheme k)
    (U : (d : ℕ) → FiniteTerminalGenealogy d) {T : FiniteTerminalGenealogy j}
    (v : FiniteCascadeRecordVertex T) (i l : ObservationLeaf T) {E : Type}
    (z : Records E (Configuration (n+1)) (finiteCascadeContinuationGraft U v)) :
    cavityRecordedLeafPairDefect s (finiteCascadeContinuationGraft U v)
      (finiteCascadeContinuationOldLeaf U v i) (finiteCascadeContinuationOldLeaf U v l) z =
      cavityRecordedLeafPairDefect s T i l (finiteCascadeContinuationRecords U v z).1 := by
  simp only [cavityRecordedLeafPairDefect,finiteCascadeContinuationOldLeaf_commonLevel,
    finiteCascadeContinuationOldLeaf_spin]

theorem cavitySingleVertex_leaf_triple_cubic (hn : 0<n) (D : AnisotropicSpinModel (n+1))
    (s : RSBScheme k) (a : ℝ) (hq : s.q 1=0) (T : FiniteTerminalGenealogy (k+2))
    (v : FiniteCascadeRecordVertex (trimRoot T)) (i l : Fin 2 → ObservationLeaf (trimRoot T))
    (j : ObservationLeaf (trimRoot T)) :
    (∫z, |cavityRecordedPairProduct s (trimRoot T) i l z.1 *
      cavitySpinOverlapDefect n
        (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
        (observationLeafSpin (trimRoot T) j z.1.2) z.2| ∂anisotropicSingleVertexMarkedLaw D s a T v) ≤
      finiteCascadeUnweightedBranchSum
        (fun d => cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s d)) (trimRoot T) +
        cavityCubicPairMoment D (Paper.parisiSchemeMeasure s) a (cavityProfileLevel s v.depth) := by
  let e := finiteCascadeContinuationExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1)) observationLinearTree (fun d => observationLinearSpin d) v
  let φ := fun z : FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (finiteCascadeContinuationGraft observationLinearTree v) =>
    ((z.1,(e z.2).1),(e z.2).2)
  let G := fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) × Configuration (n+1) =>
    |cavityRecordedPairProduct s (trimRoot T) i l z.1 * cavitySpinOverlapDefect n
      (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v))
      (observationLeafSpin (trimRoot T) j z.1.2) z.2|
  have he := measurable_finiteCascadeContinuationExtract (E:=FiniteStateField (Configuration (n+1))) (S:=Configuration (n+1))
    observationLinearTree (fun d => observationLinearSpin d) (fun d => measurable_observationLinearSpin d) v
  have hφ : Measurable φ := (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hpair : Measurable (fun z : (FiniteStateField (Configuration (n+1)) × Records (FiniteStateField (Configuration (n+1))) (Configuration (n+1)) (trimRoot T)) × Configuration (n+1) =>
      (observationLeafSpin (trimRoot T) j z.1.2,z.2)) :=
    ((measurable_observationLeafSpin (trimRoot T) j).comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd
  have hG : Measurable G :=
    ((measurable_cavityRecordedPairProduct (n:=n) s (trimRoot T) i l).comp measurable_fst |>.mul
      ((measurable_of_finite (fun z : Configuration (n+1) × Configuration (n+1) =>
        cavitySpinOverlapDefect n (cavityProfileLevel s (finiteCascadeCommonPathDepth (trimRoot T) (observationLeafVertex (trimRoot T) j) v)) z.1 z.2)).comp hpair)).abs
  have hm : (anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v))).map φ = anisotropicSingleVertexMarkedLaw D s a T v :=
    anisotropicSingleVertexMarkedLaw_eq_linear_graft D s a T v
  have hmap := integral_map (μ:=anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v))) hφ.aemeasurable hG.aestronglyMeasurable
  rw [hm] at hmap
  let ii : Fin 3 → ObservationLeaf (finiteCascadeContinuationGraft observationLinearTree v) := ![finiteCascadeContinuationOldLeaf observationLinearTree v (i 0),
    finiteCascadeContinuationOldLeaf observationLinearTree v (i 1),finiteCascadeContinuationOldLeaf observationLinearTree v j]
  let ll : Fin 3 → ObservationLeaf (finiteCascadeContinuationGraft observationLinearTree v) := ![finiteCascadeContinuationOldLeaf observationLinearTree v (l 0),
    finiteCascadeContinuationOldLeaf observationLinearTree v (l 1),
    finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth)]
  have hi : (∫z,G (φ z) ∂anisotropicTrimmedRecordedTreeLaw D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v))) =
      cavityTrimmedRecordedTripleDefectMoment D s a (.advance (finiteCascadeContinuationGraft observationLinearTree v)) ii ll := by
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp [G,φ,e,cavityRecordedPairProduct,cavityTrimmedRecordedTripleDefectMoment,ii,ll]
      simp only [cavityRecordedLeafPairDefect_continuation_old,cavityRecordedLeafPairDefect,
        finiteCascadeContinuationOldLeaf_commonLevel,finiteCascadeContinuationOldNewLeaf_commonLevel,
        finiteCascadeContinuationOldLeaf_spin,finiteCascadeContinuationNewLeaf_spin,
        linearLeaf_spin,finiteCascadeContinuationExtract_eq_records]
  rw [hmap,hi]
  have hbound := cavityTrimmedRecordedTripleDefectMoment_le_branch hn D s a hq (.advance (finiteCascadeContinuationGraft observationLinearTree v)) ii ll
  simpa only [trimRoot,finiteCascadeContinuationGraft_branchSum,observationLinearTree_branchSum,add_zero] using hbound

end QuantitativeFollowup
