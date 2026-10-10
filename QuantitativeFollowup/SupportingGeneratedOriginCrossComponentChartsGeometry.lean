module
public import QuantitativeFollowup.SupportingGeneratedOriginVertexEmbeddings
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedMixedCrossPatternsGeometry
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedCrossEdgePatternsConstruction

@[expose] public section

/-! Structural factories for two choices from the original genealogy.
The history coordinates always occur in the original choice order, even
when the concrete mixed continuation is constructed edge-first. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m M : ℕ}

def printedGeneratedComponentReindex
    (U : CavityGeneratedConstructedComponent m) (τ : Fin m → Fin M) :
    CavityGeneratedConstructedComponent M where
  depth := U.depth
  tree := U.tree
  label := fun j => (U.label j).reindex τ
  terminal_label := by rw [U.terminal_label]; rfl
  initial_label := by rw [U.initial_label]; rfl
  construction := by
    apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
    intro b e hbe
    have hj := cavityGenerated_observationCommonLevel_le U.tree b e
    obtain ⟨i,hi⟩ := U.construction.pair_clock_labels b e hbe
    have hi' : U.label ⟨observationCommonLevel U.tree b e, by omega⟩ = .mark i := by
      simpa only [cavityGeneratedFiniteClockLabels, dif_pos hj] using hi
    refine ⟨τ i, ?_⟩
    simp only [cavityGeneratedFiniteClockLabels, dif_pos hj]
    rw [hi']
    rfl

theorem printedGeneratedComponentReindex_raw
    (U : CavityGeneratedConstructedComponent m) (τ : Fin m → Fin M)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i, H (τ i) = h i) (j : ℕ) :
    (cavityGeneratedFiniteClockLabels (printedGeneratedComponentReindex U τ).label j).value H =
      (cavityGeneratedFiniteClockLabels U.label j).value h := by
  by_cases hj : j ≤ U.depth
  · simp only [printedGeneratedComponentReindex, cavityGeneratedFiniteClockLabels, dif_pos hj]
    exact CavityGeneratedClockLabel.reindex_value τ _ h H he
  · simp only [printedGeneratedComponentReindex, cavityGeneratedFiniteClockLabels, dif_neg hj,
      CavityGeneratedClockLabel.value]

theorem printedGeneratedComponentReindex_order
    (U : CavityGeneratedConstructedComponent m) (τ : Fin m → Fin M)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (H : CavityGeneratedHistory Paper.Overlap M) (he : ∀i, H (τ i) = h i)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U) :
    H ∈ nativeStreamingGeneratedComponentOrderSet (printedGeneratedComponentReindex U τ) := by
  intro j
  rw [printedGeneratedComponentReindex_raw U τ h H he,
    printedGeneratedComponentReindex_raw U τ h H he]
  exact hh j

def printedGeneratedCrossSwapIndex (m : ℕ) : Equiv.Perm (Fin (m+2)) :=
  Equiv.swap (nativeStreamingGeneratedCrossEdgeFirstMark m)
    (nativeStreamingGeneratedCrossEdgeSecondMark m)

def printedGeneratedCrossSwapComponent (U : CavityGeneratedConstructedComponent (m+2)) :
    CavityGeneratedConstructedComponent (m+2) :=
  printedGeneratedComponentReindex U (printedGeneratedCrossSwapIndex m)

theorem printedGeneratedCrossSwapIndex_append
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap) (i : Fin (m+2)) :
    (Fin.snoc (Fin.snoc h r) l : CavityGeneratedHistory Paper.Overlap (m+2))
      (printedGeneratedCrossSwapIndex m i) =
      (Fin.snoc (Fin.snoc h l) r : CavityGeneratedHistory Paper.Overlap (m+2)) i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [printedGeneratedCrossSwapIndex, nativeStreamingGeneratedCrossEdgeSecondMark,
      Equiv.swap_apply_right, nativeStreamingGeneratedCrossEdgeFirstMark,
      Fin.snoc_castSucc, Fin.snoc_last]
  · refine Fin.lastCases ?_ (fun a => ?_) j
    · simp only [printedGeneratedCrossSwapIndex, nativeStreamingGeneratedCrossEdgeFirstMark,
        Equiv.swap_apply_left, nativeStreamingGeneratedCrossEdgeSecondMark,
        Fin.snoc_last, Fin.snoc_castSucc]
    · have hfirst : a.castSucc.castSucc ≠ nativeStreamingGeneratedCrossEdgeFirstMark m := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc, nativeStreamingGeneratedCrossEdgeFirstMark, Fin.val_last] at hv
        omega
      have hsecond : a.castSucc.castSucc ≠ nativeStreamingGeneratedCrossEdgeSecondMark m := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castSucc, nativeStreamingGeneratedCrossEdgeSecondMark, Fin.val_last] at hv
        omega
      rw [printedGeneratedCrossSwapIndex, Equiv.swap_apply_of_ne_of_ne hfirst hsecond]
      simp only [Fin.snoc_castSucc]

theorem printedGeneratedCrossSwapComponent_order
    (U : CavityGeneratedConstructedComponent (m+2))
    (h : CavityGeneratedHistory Paper.Overlap m) (r l : Paper.Overlap)
    (hh : Fin.snoc (Fin.snoc h l) r ∈ nativeStreamingGeneratedComponentOrderSet U) :
    Fin.snoc (Fin.snoc h r) l ∈
      nativeStreamingGeneratedComponentOrderSet (printedGeneratedCrossSwapComponent U) :=
  printedGeneratedComponentReindex_order U (printedGeneratedCrossSwapIndex m)
    (Fin.snoc (Fin.snoc h l) r) (Fin.snoc (Fin.snoc h r) l)
    (printedGeneratedCrossSwapIndex_append h r l) hh

@[reducible] def printedGeneratedEndpointLiftEdge :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → NativeStreamingEdge T →
      NativeStreamingEdge (observationTerminalUnaryLift T)
  | _, _, .here T => .here (observationTerminalUnaryLift T)
  | _, _, .child e => .child (printedGeneratedEndpointLiftEdge e)
  | _, _, .left e => .left (printedGeneratedEndpointLiftEdge e)
  | _, _, .right e => .right (printedGeneratedEndpointLiftEdge e)

theorem printedGeneratedEndpointLiftEdge_depth {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e : NativeStreamingEdge T) : (printedGeneratedEndpointLiftEdge e).depth = e.depth+1 := by
  induction e with
  | here T => rfl
  | child e ih => exact ih
  | left e ih => exact ih
  | right e ih => exact ih

@[reducible] def printedGeneratedEndpointEdge
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree) :
    NativeStreamingEdge (nativeStreamingGeneratedEndpointComponent U).tree :=
  .child (printedGeneratedEndpointLiftEdge e)

theorem printedGeneratedEndpointEdge_depth
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree) :
    (printedGeneratedEndpointEdge U e).depth = e.depth+1 :=
  printedGeneratedEndpointLiftEdge_depth e

theorem printedGeneratedEndpointEdge_cell
    (U : CavityGeneratedConstructedComponent m) (e : NativeStreamingEdge U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : nativeStreamingGeneratedComponentClock U h (e.depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock U h e.depth) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent U) h
      ((printedGeneratedEndpointEdge U e).depth+1) ≤ r ∧
    r ≤ nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent U) h
      (printedGeneratedEndpointEdge U e).depth := by
  rw [printedGeneratedEndpointEdge_depth, nativeStreamingGeneratedEndpointComponent_clock,
    nativeStreamingGeneratedEndpointClock_succ, nativeStreamingGeneratedEndpointClock_succ]
  exact hr

end QuantitativeFollowup
