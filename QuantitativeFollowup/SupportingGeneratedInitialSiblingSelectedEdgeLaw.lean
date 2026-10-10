module
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingSelectedEdgeLawGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSelectedPatternMomentsLaw
public import QuantitativeFollowup.SupportingGeneratedInitialSiblingSelectedLawGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometry

@[expose] public section

/-! Actual original-edge marked probabilities are the complete marked
terminal projections of genuine selected-vertex laws on a unary refinement.
The original root state, every old terminal spin and all fresh marks remain. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem initialSelectedPad_firstLeaf {J : ℕ} (T : FiniteTerminalGenealogy J)
    (k : ℕ) : printedGeneratedInitialFirstLeaf (observationTreePad T k) =
      observationPadLeafEmbed T k (printedGeneratedInitialFirstLeaf T) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem initialSelectedRefinement_firstLeaf (d : ℕ → ℕ) {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    printedGeneratedInitialFirstLeaf (observationRefineTree d T) =
      observationRefinementLeafEmbed d T (printedGeneratedInitialFirstLeaf T) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      exact (initialSelectedPad_firstLeaf _ (d j)).trans
        (congrArg (observationPadLeafEmbed _ (d j)) ih)
  | fork T U ihT ihU => exact congrArg Sum.inl ihT

private theorem initialSelectedPad_descendant {J : ℕ} (T : FiniteTerminalGenealogy J)
    (k : ℕ) (v : FiniteCascadeRecordVertex T) :
    printedGeneratedInitialFirstDescendantLeaf (nativeStreamingPadVertexEmbed T k v) =
      observationPadLeafEmbed T k (printedGeneratedInitialFirstDescendantLeaf v) := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

private theorem initialSelectedBlock_descendant {J : ℕ} (T : FiniteTerminalGenealogy J)
    (k p : ℕ) :
    printedGeneratedInitialFirstDescendantLeaf (nativeStreamingBlockSelectedVertexAt T k p) =
      observationPadLeafEmbed T k (printedGeneratedInitialFirstLeaf T) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      by_cases he : p = k
      · simp only [nativeStreamingBlockSelectedVertexAt, if_pos he,
          printedGeneratedInitialFirstDescendantLeaf, printedGeneratedInitialFirstLeaf,
          observationPadLeafEmbed]
        exact initialSelectedPad_firstLeaf T k
      · simp only [nativeStreamingBlockSelectedVertexAt, if_neg he,
          printedGeneratedInitialFirstDescendantLeaf, observationPadLeafEmbed]
        exact ih

theorem printedGeneratedInitialSelectedEdge_firstDescendant (d : ℕ → ℕ)
    {J : ℕ} {T : FiniteTerminalGenealogy J} (e : NativeStreamingEdge T) (p : ℕ) :
    printedGeneratedInitialFirstDescendantLeaf (nativeStreamingEdgeSelectedVertex d e p) =
      observationRefinementLeafEmbed d T
        (printedGeneratedInitialFirstDescendantLeaf (nativeStreamingEdgeChildVertex e)) := by
  induction e with
  | here T =>
      exact (initialSelectedBlock_descendant _ _ p).trans
        (congrArg (observationPadLeafEmbed _ _) (initialSelectedRefinement_firstLeaf d T))
  | @child j T e ih =>
      exact (initialSelectedPad_descendant _ (d j) _).trans
        (congrArg (observationPadLeafEmbed _ (d j)) ih)
  | left e ih => exact congrArg Sum.inl ih
  | right e ih => exact congrArg Sum.inr ih

theorem printedGeneratedInitialSelectedEdge_clock
    (Q : ℕ → Paper.Overlap) (d : ℕ → ℕ)
    {J : ℕ} {T : FiniteTerminalGenealogy J} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    Q (nativeStreamingEdgeSelectedVertex d e p).depth =
      Q (observationRefinementDepth d e.depth+p+1) := by
  rw [nativeStreamingEdgeSelectedVertex_depth d e p hp]

def printedGeneratedInitialMarkedTerminalMap {E S A : Type} {J : ℕ}
    (T : FiniteTerminalGenealogy J) : (E × Records E S T) × A →
      (E × TerminalSpins S T) × A :=
  fun z => ((z.1.1, finiteCascadeRecordTerminalSpins T z.1.2), z.2)

theorem measurable_printedGeneratedInitialMarkedTerminalMap {E S A : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A] {J : ℕ}
    (T : FiniteTerminalGenealogy J) :
    Measurable (printedGeneratedInitialMarkedTerminalMap (E:=E) (S:=S) (A:=A) T) :=
  (measurable_fst.fst.prodMk
    ((by
      induction T with
      | leaf => exact measurable_id
      | advance T ih => exact ih.comp measurable_snd
      | fork T U ihT ihU => exact ihT.prodMap ihU :
        Measurable (finiteCascadeRecordTerminalSpins (E:=E) (S:=S) T)).comp measurable_fst.snd)).prodMk measurable_snd

def printedGeneratedInitialRefinedMarkedTerminalMap {E S A : Type}
    (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J) :
    (E × Records E S (observationRefineTree d T)) × A → (E × TerminalSpins S T) × A :=
  fun z => ((z.1.1, observationRefinementTerminalProject d T rfl
    (finiteCascadeRecordTerminalSpins (observationRefineTree d T) z.1.2)), z.2)

theorem printedGeneratedInitialRefinedMarkedTerminalMap_record {E S A : Type}
    (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (z : (E × Records E S (observationRefineTree d T)) × A) :
    printedGeneratedInitialRefinedMarkedTerminalMap d T z =
      printedGeneratedInitialMarkedTerminalMap T
        ((z.1.1, observationRefinementProject d T z.1.2), z.2) := by
  unfold printedGeneratedInitialRefinedMarkedTerminalMap printedGeneratedInitialMarkedTerminalMap
  rw [nativeStreamingRefinementTerminalProject_record]

theorem printedGeneratedInitialMarkedTerminal_refinement_map {E S A : Type}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
    (d : ℕ → ℕ) {J : ℕ} (T : FiniteTerminalGenealogy J)
    (P : Measure ((E × Records E S (observationRefineTree d T)) × A)) :
    P.map (printedGeneratedInitialRefinedMarkedTerminalMap d T) =
      (P.map (fun z => ((z.1.1, observationRefinementProject d T z.1.2), z.2))).map
        (printedGeneratedInitialMarkedTerminalMap T) := by
  have hπ : Measurable (fun z : (E × Records E S (observationRefineTree d T)) × A =>
      ((z.1.1, observationRefinementProject d T z.1.2), z.2)) :=
    (measurable_fst.fst.prodMk
      ((measurable_observationRefinementProject d T).comp measurable_fst.snd)).prodMk measurable_snd
  rw [Measure.map_map (measurable_printedGeneratedInitialMarkedTerminalMap T) hπ]
  congr 1
  funext z
  exact printedGeneratedInitialRefinedMarkedTerminalMap_record d T z

theorem printedGeneratedInitialSelectedEdge_single_terminal_law {n J : ℕ}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀ i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingSingleVertexLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (printedGeneratedInitialRefinedMarkedTerminalMap d T) =
      (nativeStreamingEdgeSingleMarkProbability D μ a q T e
        (Q (observationRefinementDepth d e.depth+p+1)) : Measure _).map
          (printedGeneratedInitialMarkedTerminalMap T) := by
  rw [printedGeneratedInitialMarkedTerminal_refinement_map,
    nativeStreamingSelectedSingleLaw_projection_eq_edge_probability
      D μ a q Q d hQ hlevels hzero T e p hp]

theorem printedGeneratedInitialSelectedEdge_current_terminal_law {n J : ℕ}
    (D : AnisotropicSpinModel n) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀ i, Q (observationRefinementDepth d i) = q i) (hzero : q 0 = 1)
    (T : FiniteTerminalGenealogy J) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p < d e.depth) :
    (nativeStreamingCurrentPairLaw D μ a Q (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p)).map
        (printedGeneratedInitialRefinedMarkedTerminalMap d T) =
      (nativeStreamingEdgeCurrentPairProbability D μ a q T e
        (Q (observationRefinementDepth d e.depth+p+1)) : Measure _).map
          (printedGeneratedInitialMarkedTerminalMap T) := by
  rw [printedGeneratedInitialMarkedTerminal_refinement_map,
    nativeStreamingSelectedCurrentLaw_projection_eq_edge_probability
      D μ a q Q d hQ hlevels hzero T e p hp]

end QuantitativeFollowup
