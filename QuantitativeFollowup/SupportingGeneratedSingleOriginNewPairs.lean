module
public import QuantitativeFollowup.SupportingGeneratedSingleOriginOldPairs
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinedVertexPatternMoments

@[expose] public section

/-! The new defect produced by a single-origin chart is the defect of its
actual chosen terminal leaves at their physical common clock. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

private theorem endpointLiftLeaf_injective {J : ℕ} (T : FiniteTerminalGenealogy J) :
    Function.Injective (nativeStreamingEndpointLiftLeaf T) := by
  induction T with
  | leaf => exact Function.injective_id
  | advance T ih => exact ih
  | fork T U ihT ihU => exact Sum.map_injective.mpr ⟨ihT,ihU⟩

theorem printedGeneratedOriginChartOldLeaf_injective
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (k : NativeStreamingGeneratedVertexKind) :
    Function.Injective (printedGeneratedOriginChartOldLeaf U γ k) := by
  rcases γ with i | (i | u)
  · exact finiteCascadeContinuationOldLeaf_injective k.continuation _
  · exact (finiteCascadeContinuationOldLeaf_injective k.continuation _).comp
      (observationRefinementLeafEmbed_injective _ U.tree)
  · exact (finiteCascadeContinuationOldLeaf_injective k.continuation _).comp
      (endpointLiftLeaf_injective U.tree)

theorem nativeStreamingGeneratedContinuationTerminalMap_new_leaf {S : Type}
    (U : (j : ℕ) → FiniteTerminalGenealogy j) {J : ℕ} {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf (U v.depth))
    (σ : TerminalSpins S (finiteCascadeContinuationGraft U v)) :
    observationTerminalSpin (U v.depth) i (nativeStreamingGeneratedContinuationTerminalMap U v σ).2 =
      observationTerminalSpin (finiteCascadeContinuationGraft U v)
        (finiteCascadeContinuationNewLeaf U v i) σ := by
  induction v with
  | root T => rfl
  | child v ih => exact ih i σ
  | left v ih => exact ih i σ.1
  | right v ih => exact ih i σ.2

theorem nativeStreamingGeneratedVertexTerminalProjection_single_new_leaf {S : Type}
    {J : ℕ} {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft observationLinearTree v)) :
    (nativeStreamingGeneratedVertexTerminalProjection .single v σ).2 =
      observationTerminalSpin (finiteCascadeContinuationGraft observationLinearTree v)
        (finiteCascadeContinuationNewLeaf observationLinearTree v (observationLinearLeaf v.depth)) σ :=
  nativeStreamingGeneratedContinuationTerminalMap_new_leaf observationLinearTree v _ σ

def printedGeneratedOriginChartFreshLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) :
    ObservationLeaf (printedGeneratedOriginChartComponent U γ .single).tree :=
  match γ with
  | .inl i => finiteCascadeContinuationNewLeaf observationLinearTree (printedGeneratedOriginChartFork U i)
      (observationLinearLeaf (printedGeneratedOriginChartFork U i).depth)
  | .inr (.inl i) => finiteCascadeContinuationNewLeaf observationLinearTree
      (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
      (observationLinearLeaf (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i)).depth)
  | .inr (.inr _) => finiteCascadeContinuationNewLeaf observationLinearTree
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (observationLinearLeaf (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth)

def printedGeneratedOriginChartCurrentLeaf (U : CavityGeneratedConstructedComponent m)
    (γ : PrintedGeneratedOriginChart U) (b : Bool) :
    ObservationLeaf (printedGeneratedOriginChartComponent U γ .current).tree :=
  match γ with
  | .inl i => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree (printedGeneratedOriginChartFork U i)
      (if b then Sum.inr (observationLinearLeaf (printedGeneratedOriginChartFork U i).depth)
        else Sum.inl (observationLinearLeaf (printedGeneratedOriginChartFork U i).depth))
  | .inr (.inl i) => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
      (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i))
      (if b then Sum.inr (observationLinearLeaf (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i)).depth)
        else Sum.inl (observationLinearLeaf (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U i)).depth))
  | .inr (.inr _) => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (if b then Sum.inr (observationLinearLeaf (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth)
        else Sum.inl (observationLinearLeaf (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth))

theorem printedGeneratedOriginChartOldLeaf_ne_fresh
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (i : ObservationLeaf U.tree) :
    printedGeneratedOriginChartOldLeaf U γ .single i ≠ printedGeneratedOriginChartFreshLeaf U γ := by
  rcases γ with v | (e | u)
  all_goals exact finiteCascadeContinuationOldNewLeaf_ne observationLinearTree _ _ _

theorem printedGeneratedOriginChartCurrentLeaves_ne
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U) :
    printedGeneratedOriginChartCurrentLeaf U γ false ≠ printedGeneratedOriginChartCurrentLeaf U γ true := by
  rcases γ with v | (e | u)
  all_goals
    intro he
    have hn := (finiteCascadeContinuationNewLeaf_injective nativeStreamingCurrentPairTree _) he
    cases hn

theorem printedGeneratedOriginChartTerminalProject_fresh_leaf
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .single)) :
    (printedGeneratedOriginChartTerminalProject U γ .single σ).2 =
      observationTerminalSpin (printedGeneratedOriginChartComponent U γ .single).tree
        (printedGeneratedOriginChartFreshLeaf U γ) σ := by
  rcases γ with i | (i | u)
  all_goals exact nativeStreamingGeneratedVertexTerminalProjection_single_new_leaf _ σ

theorem nativeStreamingGeneratedVertexTerminalProjection_current_new_leaf {S : Type}
    {J : ℕ} {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T)
    (σ : TerminalSpins S (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)) (b : Bool) :
    (if b then (nativeStreamingGeneratedVertexTerminalProjection .current v σ).2.2
      else (nativeStreamingGeneratedVertexTerminalProjection .current v σ).2.1) =
      observationTerminalSpin (finiteCascadeContinuationGraft nativeStreamingCurrentPairTree v)
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree v
          (if b then Sum.inr (observationLinearLeaf v.depth) else Sum.inl (observationLinearLeaf v.depth))) σ := by
  cases b
  · exact nativeStreamingGeneratedContinuationTerminalMap_new_leaf nativeStreamingCurrentPairTree v
      (Sum.inl (observationLinearLeaf v.depth)) σ
  · exact nativeStreamingGeneratedContinuationTerminalMap_new_leaf nativeStreamingCurrentPairTree v
      (Sum.inr (observationLinearLeaf v.depth)) σ

theorem printedGeneratedOriginChartTerminalProject_current_leaf
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .current)) (b : Bool) :
    (if b then (printedGeneratedOriginChartTerminalProject U γ .current σ).2.2
      else (printedGeneratedOriginChartTerminalProject U γ .current σ).2.1) =
      observationTerminalSpin (printedGeneratedOriginChartComponent U γ .current).tree
        (printedGeneratedOriginChartCurrentLeaf U γ b) σ := by
  rcases γ with i | (i | u)
  all_goals exact nativeStreamingGeneratedVertexTerminalProjection_current_new_leaf _ σ b

theorem printedGeneratedOriginChartOldFresh_commonClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) (i : ObservationLeaf U.tree) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .single)
      (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
      (observationCommonLevel (printedGeneratedOriginChartComponent U γ .single).tree
        (printedGeneratedOriginChartOldLeaf U γ .single i) (printedGeneratedOriginChartFreshLeaf U γ)) =
      nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (printedGeneratedOriginChartOrigin U γ r) := by
  rcases γ with v | (e | u)
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent U (printedGeneratedOriginChartFork U v)
        (printedGeneratedOriginChartFork_interior U v).1
        (printedGeneratedOriginChartFork_interior U v).2 .single)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U v).depth))
      (observationCommonLevel _ (finiteCascadeContinuationOldLeaf observationLinearTree _ i)
        (finiteCascadeContinuationNewLeaf observationLinearTree _ _)) = _
    rw [finiteCascadeContinuationOldNewLeaf_commonLevel,
      printedGeneratedVertexComponent_snoc_clock U _ _ _ .single h hh]
    rfl
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEdgeComponent U (printedGeneratedOriginChartEdge U e) .single) (Fin.snoc h r)
      (observationCommonLevel _
        (finiteCascadeContinuationOldLeaf observationLinearTree _
          (nativeStreamingGeneratedEdgeLeaf U (printedGeneratedOriginChartEdge U e) i))
        (finiteCascadeContinuationNewLeaf observationLinearTree _ _)) = _
    rw [finiteCascadeContinuationOldNewLeaf_commonLevel,
      nativeStreamingGeneratedEdgeComponent_clock,
      nativeStreamingGeneratedEdgeObservedComponent_clock_snoc U _ h r hh hr]
    change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h)
      (printedGeneratedOriginChartEdge U e).depth r
      (finiteCascadeCommonPathDepth _
        (observationLeafVertex _ (observationRefinementLeafEmbed _ U.tree i))
        (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U e))) = _
    rw [nativeStreamingRefinementLeafEmbed_vertex]
    change nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h)
      (printedGeneratedOriginChartEdge U e).depth r
      (finiteCascadeCommonPathDepth
        (observationRefineTree (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U e).depth) U.tree)
        (nativeStreamingRefinementVertexEmbed
          (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U e).depth) U.tree
          (observationLeafVertex U.tree i))
        (nativeStreamingEdgeRefinedVertex
          (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U e).depth)
          (printedGeneratedOriginChartEdge U e))) = _
    rw [←nativeStreamingSelected_one_slot_vertex]
    exact nativeStreamingEdgeOldLeaf_commonPathClock_eq_mark
      (nativeStreamingEdgeSubdivision (printedGeneratedOriginChartEdge U e).depth)
      (nativeStreamingGeneratedComponentClock U h)
      (nativeStreamingEdgeSchedule (nativeStreamingGeneratedComponentClock U h)
        (printedGeneratedOriginChartEdge U e).depth r) U.tree
      (fun j _ => nativeStreamingEdgeSchedule_refinement _ _ _ j) i _ 0
      (by simp [nativeStreamingEdgeSubdivision]) r
      (by simp only [Nat.add_zero,nativeStreamingEdgeSubdivision_depth,le_refl,if_true,
        nativeStreamingEdgeSchedule_inserted])
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hs := printedGeneratedVertexComponent_snoc_clock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 .single h hhp
    rw [nativeStreamingGeneratedEndpointVertex_clock] at hs
    change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 .single)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth))
      (observationCommonLevel _
        (finiteCascadeContinuationOldLeaf observationLinearTree _ (nativeStreamingGeneratedEndpointLeaf U i))
        (finiteCascadeContinuationNewLeaf observationLinearTree _ _)) = _
    rw [finiteCascadeContinuationOldNewLeaf_commonLevel,hs]
    exact nativeStreamingGeneratedEndpointLeaf_vertex_commonClock U h (.root U.tree) i

theorem printedGeneratedOriginChartCurrentLeaves_commonClock
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) :
    nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .current)
      (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
      (observationCommonLevel (printedGeneratedOriginChartComponent U γ .current).tree
        (printedGeneratedOriginChartCurrentLeaf U γ false) (printedGeneratedOriginChartCurrentLeaf U γ true)) =
      nativeStreamingOriginLevel (nativeStreamingGeneratedComponentClock U h)
        (printedGeneratedOriginChartOrigin U γ r) := by
  rcases γ with v | (e | u)
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent U (printedGeneratedOriginChartFork U v)
        (printedGeneratedOriginChartFork_interior U v).1
        (printedGeneratedOriginChartFork_interior U v).2 .current)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h (printedGeneratedOriginChartFork U v).depth))
      (observationCommonLevel _
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (printedGeneratedOriginChartFork U v) (Sum.inl (observationLinearLeaf (printedGeneratedOriginChartFork U v).depth)))
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (printedGeneratedOriginChartFork U v) (Sum.inr (observationLinearLeaf (printedGeneratedOriginChartFork U v).depth)))) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel,
      printedGeneratedVertexComponent_snoc_clock U _ _ _ .current h hh]
    rfl
  · change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedEdgeComponent U (printedGeneratedOriginChartEdge U e) .current) (Fin.snoc h r)
      (observationCommonLevel _
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U e))
          (Sum.inl (observationLinearLeaf (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U e)).depth)))
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U e))
          (Sum.inr (observationLinearLeaf (nativeStreamingGeneratedEdgeVertex U (printedGeneratedOriginChartEdge U e)).depth)))) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel,nativeStreamingGeneratedEdgeComponent_clock]
    exact nativeStreamingGeneratedEdge_selected_clock U _ h r hh hr
  · have hhp : h ∈ nativeStreamingGeneratedComponentOrderSet (nativeStreamingGeneratedEndpointComponent U) := by
      rwa [nativeStreamingGeneratedEndpointComponent_orderSet]
    have hs := printedGeneratedVertexComponent_snoc_clock (nativeStreamingGeneratedEndpointComponent U)
      (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
      (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 .current h hhp
    rw [nativeStreamingGeneratedEndpointVertex_clock] at hs
    change nativeStreamingGeneratedComponentClock
      (nativeStreamingGeneratedVertexComponent (nativeStreamingGeneratedEndpointComponent U)
        (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).1
        (nativeStreamingGeneratedEndpointVertex_interior U (.root U.tree)).2 .current)
      (Fin.snoc h (nativeStreamingGeneratedComponentClock U h U.depth))
      (observationCommonLevel _
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (Sum.inl (observationLinearLeaf (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth)))
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
          (nativeStreamingGeneratedEndpointVertex U (.root U.tree))
          (Sum.inr (observationLinearLeaf (nativeStreamingGeneratedEndpointVertex U (.root U.tree)).depth)))) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel,hs]
    exact nativeStreamingGeneratedEndpointVertex_clock U h (.root U.tree)

theorem printedGeneratedOriginChartOriginalFresh_defect
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) (i : ObservationLeaf U.tree)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .single)) :
    cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (printedGeneratedOriginChartOrigin U γ r))
      (observationTerminalSpin U.tree i (printedGeneratedOriginChartTerminalProject U γ .single σ).1)
      (printedGeneratedOriginChartTerminalProject U γ .single σ).2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .single)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
        (observationCommonLevel (printedGeneratedOriginChartComponent U γ .single).tree
          (printedGeneratedOriginChartOldLeaf U γ .single i) (printedGeneratedOriginChartFreshLeaf U γ)))
      (observationTerminalSpin _ (printedGeneratedOriginChartOldLeaf U γ .single i) σ)
      (observationTerminalSpin _ (printedGeneratedOriginChartFreshLeaf U γ) σ) := by
  rw [printedGeneratedOriginChartOldFresh_commonClock U γ h r hh hr,
    printedGeneratedOriginChartTerminalProject_old_leaf,printedGeneratedOriginChartTerminalProject_fresh_leaf]

theorem printedGeneratedOriginChartCurrent_defect
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .current)) :
    cavitySpinOverlapDefect n
      (nativeStreamingOriginLevel (nativeStreamingGeneratedComponentClock U h)
        (printedGeneratedOriginChartOrigin U γ r))
      (printedGeneratedOriginChartTerminalProject U γ .current σ).2.1
      (printedGeneratedOriginChartTerminalProject U γ .current σ).2.2 =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .current)
        (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
        (observationCommonLevel (printedGeneratedOriginChartComponent U γ .current).tree
          (printedGeneratedOriginChartCurrentLeaf U γ false) (printedGeneratedOriginChartCurrentLeaf U γ true)))
      (observationTerminalSpin _ (printedGeneratedOriginChartCurrentLeaf U γ false) σ)
      (observationTerminalSpin _ (printedGeneratedOriginChartCurrentLeaf U γ true) σ) := by
  rw [printedGeneratedOriginChartCurrentLeaves_commonClock U γ h r hh hr,
    ←printedGeneratedOriginChartTerminalProject_current_leaf U γ σ false,
    ←printedGeneratedOriginChartTerminalProject_current_leaf U γ σ true]
  rfl

theorem printedGeneratedOriginChartOriginalFresh_test
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r) (i : ObservationLeaf U.tree)
    (F : CavityGeneratedComponentTerminal n U → ℝ)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .single)) :
    nativeStreamingOriginalFreshSpinTest U.tree F i
      (nativeStreamingOriginCommonClock (nativeStreamingGeneratedComponentClock U h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (printedGeneratedOriginChartOrigin U γ r))
      (printedGeneratedOriginChartTerminalProject U γ .single σ) =
    F (printedGeneratedOriginChartTerminalProject U γ .single σ).1 *
      cavitySpinOverlapDefect n
        (nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .single)
          (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
          (observationCommonLevel (printedGeneratedOriginChartComponent U γ .single).tree
            (printedGeneratedOriginChartOldLeaf U γ .single i) (printedGeneratedOriginChartFreshLeaf U γ)))
        (observationTerminalSpin _ (printedGeneratedOriginChartOldLeaf U γ .single i) σ)
        (observationTerminalSpin _ (printedGeneratedOriginChartFreshLeaf U γ) σ) := by
  unfold nativeStreamingOriginalFreshSpinTest
  rw [printedGeneratedOriginChartOriginalFresh_defect U γ h r hh hr]

theorem printedGeneratedOriginChartCurrent_test
    (U : CavityGeneratedConstructedComponent m) (γ : PrintedGeneratedOriginChart U)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hh : h ∈ nativeStreamingGeneratedComponentOrderSet U)
    (hr : printedGeneratedOriginChartCell U γ h r)
    (F : CavityGeneratedComponentTerminal n U → ℝ)
    (σ : CavityGeneratedComponentTerminal n (printedGeneratedOriginChartComponent U γ .current)) :
    nativeStreamingDefectSpinTest U.tree F
      (nativeStreamingOriginLevel (nativeStreamingGeneratedComponentClock U h)
        (printedGeneratedOriginChartOrigin U γ r))
      (printedGeneratedOriginChartTerminalProject U γ .current σ) =
    F (printedGeneratedOriginChartTerminalProject U γ .current σ).1 *
      cavitySpinOverlapDefect n
        (nativeStreamingGeneratedComponentClock (printedGeneratedOriginChartComponent U γ .current)
          (Fin.snoc h (printedGeneratedOriginChartClock U γ h r))
          (observationCommonLevel (printedGeneratedOriginChartComponent U γ .current).tree
            (printedGeneratedOriginChartCurrentLeaf U γ false) (printedGeneratedOriginChartCurrentLeaf U γ true)))
        (observationTerminalSpin _ (printedGeneratedOriginChartCurrentLeaf U γ false) σ)
        (observationTerminalSpin _ (printedGeneratedOriginChartCurrentLeaf U γ true) σ) := by
  unfold nativeStreamingDefectSpinTest
  rw [printedGeneratedOriginChartCurrent_defect U γ h r hh hr]

end QuantitativeFollowup
