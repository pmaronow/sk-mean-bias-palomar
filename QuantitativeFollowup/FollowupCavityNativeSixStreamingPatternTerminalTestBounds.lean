module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternTerminalRepresentationFuture
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternNormalizerTerminalRepresentation

@[expose] public section

/-! Uniform structural bounds for the actual fixed terminal tests.
Every old test is evaluated through its genuine terminal projection. A
single defect contributes at most two, and every connected graft adds at
most two leaves. The bounds include arbitrary refinements, coincident
selected vertices and every section of an observation pair tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPatternVertexTerminalTest_originalFresh_abs_le
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C)
    (i : ObservationLeaf T) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft observationLinearTree v)) :
    |nativeStreamingPatternVertexTerminalTest .single T v
      (nativeStreamingOriginalFreshSpinTest T F i q) σ| ≤ 2*C := by
  exact nativeStreamingOriginalFreshSpinTest_abs_le T F C hC hF i q
    (nativeStreamingGeneratedVertexTerminalProjection .single v σ)

theorem nativeStreamingPatternVertexTerminalTest_current_abs_le
    (T : FiniteTerminalGenealogy J) (v : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)) :
    |nativeStreamingPatternVertexTerminalTest .current T v
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (nativeStreamingGeneratedVertexTerminalProjection .current v σ)

theorem nativeStreamingPatternCrossTerminalTest_defect_abs_le
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    |nativeStreamingPatternCrossTerminalTest T v w
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (nativeStreamingPatternCrossTerminalProjection v w σ)

theorem nativeStreamingPatternRefinedVertexTerminalTest_originalFresh_abs_le
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C)
    (i : ObservationLeaf T) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft observationLinearTree v)) :
    |nativeStreamingPatternRefinedVertexTerminalTest .single d T v
      (nativeStreamingOriginalFreshSpinTest T F i q) σ| ≤ 2*C := by
  let z := nativeStreamingGeneratedVertexTerminalProjection .single v σ
  exact nativeStreamingOriginalFreshSpinTest_abs_le T F C hC hF i q
    (observationRefinementTerminalProject d T rfl z.1,z.2)

theorem nativeStreamingPatternRefinedVertexTerminalTest_current_abs_le
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)) :
    |nativeStreamingPatternRefinedVertexTerminalTest .current d T v
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  let z := nativeStreamingGeneratedVertexTerminalProjection .current v σ
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (observationRefinementTerminalProject d T rfl z.1,z.2)

theorem nativeStreamingPatternRefinedCrossTerminalTest_defect_abs_le
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex (observationRefineTree d T))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeCrossContinuationGraft observationLinearTree v w)) :
    |nativeStreamingPatternRefinedCrossTerminalTest d T v w
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  let z := nativeStreamingPatternCrossTerminalProjection v w σ
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (observationRefinementTerminalProject d T rfl z.1,z.2)

theorem nativeStreamingPatternPairContinuationTerminalTest_defect_abs_le
    (P : (j : ℕ) → ObservationPairTree j) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft (fun j => (P j).tree) v)) :
    |nativeStreamingPatternPairContinuationTerminalTest P T v
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (nativeStreamingPatternPairContinuationTerminalProjection P v σ)

theorem nativeStreamingPatternRefinedPairTerminalTest_defect_abs_le
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : (j : ℕ) → ObservationPairTree j)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T))
    (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀σ, |F σ| ≤ C) (q : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1))
      (finiteCascadeContinuationGraft (fun j => (P j).tree) v)) :
    |nativeStreamingPatternRefinedPairTerminalTest d T P v
      (nativeStreamingDefectSpinTest T F q) σ| ≤ 2*C := by
  let z := nativeStreamingPatternPairContinuationTerminalProjection P v σ
  exact nativeStreamingDefectSpinTest_abs_le T F C hC hF q
    (observationRefinementTerminalProject d T rfl z.1,z.2)

theorem nativeStreamingNormalizerBinaryTerminalTest_abs_le
    (n : ℕ) (l : Paper.Overlap)
    (σ : TerminalSpins (Configuration (n+1)) anisotropicBinaryObservationTree) :
    |nativeStreamingNormalizerBinaryTerminalTest n l σ| ≤ 2 :=
  cavitySpinOverlapDefect_abs_le_two n l l.property σ.1 σ.2

theorem nativeStreamingPatternVertexTree_leafCount_le
    (k : NativeStreamingGeneratedVertexKind) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft k.continuation v)) ≤
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  rw [finiteCascadeContinuationGraft_leafCount]
  cases k with
  | single =>
      simp only [NativeStreamingGeneratedVertexKind.continuation,observationLinearTree_leafCount]
      omega
  | current =>
      simp only [NativeStreamingGeneratedVertexKind.continuation,nativeStreamingCurrentPairTree,
        asGenealogy,FiniteCascadeGenealogy.leafCount,observationLinearTree_leafCount]
      omega

theorem nativeStreamingPatternCrossTree_leafCount
    (T : FiniteTerminalGenealogy J) (v w : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (finiteCascadeCrossContinuationGraft observationLinearTree v w)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  rw [finiteCascadeCrossContinuationGraft,finiteCascadeContinuationGraft_leafCount,
    finiteCascadeContinuationGraft_leafCount,observationLinearTree_leafCount,
    observationLinearTree_leafCount]

theorem nativeStreamingPatternPairTree_leafCount
    (P : (j : ℕ) → ObservationPairTree j) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex T) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (finiteCascadeContinuationGraft (fun j => (P j).tree) v)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  rw [finiteCascadeContinuationGraft_leafCount,observationPairTree_leafCount]

theorem nativeStreamingPatternRefinedVertexTree_leafCount_le
    (k : NativeStreamingGeneratedVertexKind) (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) :
    FiniteCascadeGenealogy.leafCount (asGenealogy (finiteCascadeContinuationGraft k.continuation v)) ≤
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  simpa only [leafCount_observationRefineTree] using
    nativeStreamingPatternVertexTree_leafCount_le k (observationRefineTree d T) v

theorem nativeStreamingPatternRefinedCrossTree_leafCount
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (v w : FiniteCascadeRecordVertex (observationRefineTree d T)) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (finiteCascadeCrossContinuationGraft observationLinearTree v w)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  simpa only [leafCount_observationRefineTree] using
    nativeStreamingPatternCrossTree_leafCount (observationRefineTree d T) v w

theorem nativeStreamingPatternRefinedPairTree_leafCount
    (d : ℕ → ℕ) (T : FiniteTerminalGenealogy J)
    (P : (j : ℕ) → ObservationPairTree j)
    (v : FiniteCascadeRecordVertex (observationRefineTree d T)) :
    FiniteCascadeGenealogy.leafCount
      (asGenealogy (finiteCascadeContinuationGraft (fun j => (P j).tree) v)) =
      FiniteCascadeGenealogy.leafCount (asGenealogy T)+2 := by
  simpa only [leafCount_observationRefineTree] using
    nativeStreamingPatternPairTree_leafCount P (observationRefineTree d T) v

theorem nativeStreamingNormalizerBinaryTree_leafCount :
    FiniteCascadeGenealogy.leafCount (asGenealogy anisotropicBinaryObservationTree) = 2 := rfl

end QuantitativeFollowup
