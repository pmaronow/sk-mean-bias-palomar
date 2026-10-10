module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentationRefinement

@[expose] public section

/-! Shared-future marks are the actual two leaves of their continuation
tree.  The genuine inserted-time probabilities, including their canonical
equal-time slots and fallback split, are represented by terminal tests on
these enlarged native genealogies. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def nativeStreamingPatternPairTerminalMarks {S : Type} {d : ℕ}
    (P : ObservationPairTree d) (σ : TerminalSpins S P.tree) : S × S :=
  (observationTerminalSpin P.tree (observationPairFirstLeaf P) σ,
    observationTerminalSpin P.tree (observationPairSecondLeaf P) σ)

theorem nativeStreamingPatternPairTerminalMarks_record {E S : Type} {d : ℕ}
    (P : ObservationPairTree d) (z : Records E S P.tree) :
    nativeStreamingPatternPairTerminalMarks P (finiteCascadeRecordTerminalSpins P.tree z) =
      P.spins z := by
  rw [nativeStreamingPatternPairTerminalMarks, observationTerminalSpin_record,
    observationTerminalSpin_record]
  exact (observationPair_spins_eq_leaf_pair P z).symm

def nativeStreamingPatternPairContinuationTerminalProjection {S : Type}
    (P : (d : ℕ) → ObservationPairTree d) {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft (fun d => (P d).tree) v)) :
    TerminalSpins S T × (S × S) :=
  let z := nativeStreamingGeneratedContinuationTerminalMap (fun d => (P d).tree) v σ
  (z.1,nativeStreamingPatternPairTerminalMarks (P v.depth) z.2)

theorem nativeStreamingPatternPairContinuationTerminalProjection_record {E S : Type}
    (P : (d : ℕ) → ObservationPairTree d) {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T)
    (z : Records E S (finiteCascadeContinuationGraft (fun d => (P d).tree) v)) :
    nativeStreamingPatternPairContinuationTerminalProjection P v
      (finiteCascadeRecordTerminalSpins _ z) =
      (finiteCascadeRecordTerminalSpins T
        (finiteCascadeContinuationExtract (fun d => (P d).tree) (fun d => (P d).spins) v z).1,
        (finiteCascadeContinuationExtract (fun d => (P d).tree) (fun d => (P d).spins) v z).2) := by
  dsimp only [nativeStreamingPatternPairContinuationTerminalProjection]
  rw [nativeStreamingGeneratedContinuationTerminalMap_record]
  dsimp only
  rw [nativeStreamingPatternPairTerminalMarks_record,finiteCascadeContinuationExtract_eq_records]

def nativeStreamingPatternPairContinuationTerminalTest
    (P : (d : ℕ) → ObservationPairTree d) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :=
  G ∘ nativeStreamingPatternPairContinuationTerminalProjection P v

theorem nativeStreamingPairContinuationMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (P : (d : ℕ) → ObservationPairTree d)
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (G : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment
      (nativeStreamingActualContinuationProbability D μ a q
        (fun d => (P d).tree) (fun d => (P d).spins) T v) G =
      nativeStreamingOldTerminalExpectation D μ a q
        (finiteCascadeContinuationGraft (fun d => (P d).tree) v)
        (nativeStreamingPatternPairContinuationTerminalTest P T v G) := by
  let ψ := fun z : AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1))
        (finiteCascadeContinuationGraft (fun d => (P d).tree) v) =>
    ((z.1,(finiteCascadeContinuationExtract (fun d => (P d).tree)
      (fun d => (P d).spins) v z.2).1),
      (finiteCascadeContinuationExtract (fun d => (P d).tree) (fun d => (P d).spins) v z.2).2)
  have he := measurable_finiteCascadeContinuationExtract (E:=AnisotropicObservationState (n+1))
    (S:=Configuration (n+1)) (fun d => (P d).tree) (fun d => (P d).spins)
    (fun d => (P d).measurable_spins) v
  have hm : Measurable ψ :=
    (measurable_fst.prodMk (he.fst.comp measurable_snd)).prodMk (he.snd.comp measurable_snd)
  have hc : Continuous (fun z : ((AnisotropicObservationState (n+1) ×
      Records (AnisotropicObservationState (n+1)) (Configuration (n+1)) T) ×
        (Configuration (n+1) × Configuration (n+1))) =>
      G (finiteCascadeRecordTerminalSpins T z.1.2,z.2)) :=
    (continuous_of_discreteTopology (f:=G)).comp
      (((continuous_finiteCascadeRecordTerminalSpins T).comp continuous_fst.snd).prodMk continuous_snd)
  unfold nativeStreamingTerminalMarkMoment nativeStreamingActualContinuationProbability
  rw [ProbabilityMeasure.toMeasure_map,integral_map hm.aemeasurable hc.aestronglyMeasurable]
  unfold nativeStreamingOldTerminalExpectation nativeStreamingPatternPairContinuationTerminalTest
  apply integral_congr_ae
  exact .of_forall fun z => congrArg G
    (nativeStreamingPatternPairContinuationTerminalProjection_record P v z.2).symm

def nativeStreamingPatternRefinedPairTerminalTest
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J) (P : (j : ℕ) → ObservationPairTree j)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (G : TerminalSpins (Configuration n) T × (Configuration n × Configuration n) → ℝ) :=
  nativeStreamingPatternPairContinuationTerminalTest P (observationRefineTree d T) v
    (nativeStreamingPatternRefinedMarkedTest d T G)

theorem nativeStreamingRefinedPairContinuationMoment_eq_oldTerminalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : (j : ℕ) → ObservationPairTree j)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (G : TerminalSpins (Configuration (n+1)) T ×
      (Configuration (n+1) × Configuration (n+1)) → ℝ) :
    nativeStreamingTerminalMarkMoment
      ((nativeStreamingActualContinuationProbability D μ a Q
        (fun j => (P j).tree) (fun j => (P j).spins) (observationRefineTree d T) v).map
          (fun z => ((z.1.1,observationRefinementProject d T z.1.2),z.2))) G =
      nativeStreamingOldTerminalExpectation D μ a Q
        (finiteCascadeContinuationGraft (fun j => (P j).tree) v)
        (nativeStreamingPatternRefinedPairTerminalTest d T P v G) := by
  rw [nativeStreamingPatternTerminalMarkMoment_refinement_map]
  exact nativeStreamingPairContinuationMoment_eq_oldTerminalExpectation
    D μ a Q P (observationRefineTree d T) v _

theorem nativeStreamingPatternMoment_future_vertex_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (v : FiniteCascadeRecordVertex T) (j : ℕ) (l : Paper.Overlap) :
    nativeStreamingPatternMoment D μ a q T F (.future (.vertex v) j l) =
      nativeStreamingOldTerminalExpectation D μ a (nativeStreamingEdgeSchedule q j l)
        (finiteCascadeFutureVertexGraft
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v) (j+1))
        (nativeStreamingPatternRefinedPairTerminalTest (nativeStreamingEdgeSubdivision j) T
          (finiteCascadeFuturePairTree (j+1))
          (nativeStreamingRefinementVertexEmbed (nativeStreamingEdgeSubdivision j) T v)
          (nativeStreamingDefectSpinTest T F l)) := by
  exact nativeStreamingRefinedPairContinuationMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingEdgeSchedule q j l) (nativeStreamingEdgeSubdivision j) T
    (finiteCascadeFuturePairTree (j+1)) _ _

theorem nativeStreamingPatternMoment_future_edge_terminalRepresentation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (e : NativeStreamingEdge T) (r : Paper.Overlap) (j : ℕ) (l : Paper.Overlap) :
    let d := nativeStreamingPairObservationSubdivision
    let v := nativeStreamingEdgeSelectedVertex d e (nativeStreamingPairObservationIndex e.depth j r l)
    let split := observationRefinementDepth d j + nativeStreamingPairObservationIndex j e.depth l r + 1
    nativeStreamingPatternMoment D μ a q T F (.future (.edge e r) j l) =
      nativeStreamingOldTerminalExpectation D μ a
        (nativeStreamingPairObservationSchedule q e.depth j r l)
        (finiteCascadeFutureVertexGraft v split)
        (nativeStreamingPatternRefinedPairTerminalTest d T
          (finiteCascadeFuturePairTree split) v (nativeStreamingDefectSpinTest T F l)) := by
  dsimp only
  exact nativeStreamingRefinedPairContinuationMoment_eq_oldTerminalExpectation D μ a
    (nativeStreamingPairObservationSchedule q e.depth j r l)
    nativeStreamingPairObservationSubdivision T _ _ _

end QuantitativeFollowup
