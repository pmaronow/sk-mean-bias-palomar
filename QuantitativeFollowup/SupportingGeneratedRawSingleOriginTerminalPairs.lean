module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginCharts
public import QuantitativeFollowup.SupportingGeneratedRawVertexTerminalPairs

@[expose] public section

/-! The raw origin charts retain every original terminal coordinate and
its physical pair clock. Their fresh leaves give the literal single/current
defects, including endpoint origins and repeated observation times. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

def cavityGeneratedObservedRawChartTerminalProject {S : Type}
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    TerminalSpins S (cavityGeneratedObservedRawChartComponent U γ k).tree → TerminalSpins S U.tree × k.Mark S :=
  match γ with
  | .inl i => nativeStreamingGeneratedVertexTerminalProjection k (cavityGeneratedObservedRawChartFork U i)
  | .inr (.inl i) => fun σ =>
      let z := nativeStreamingGeneratedVertexTerminalProjection k
        (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
          (cavityGeneratedObservedRawChartEdge U i)) σ
      (observationRefinementTerminalProject (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        U.tree rfl z.1,z.2)
  | .inr (.inr _) => nativeStreamingGeneratedVertexTerminalProjection k (.root U.tree)

def cavityGeneratedObservedRawChartOldLeaf
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (i : ObservationLeaf U.tree) :
    ObservationLeaf (cavityGeneratedObservedRawChartComponent U γ k).tree :=
  match γ with
  | .inl j => finiteCascadeContinuationOldLeaf k.continuation (cavityGeneratedObservedRawChartFork U j) i
  | .inr (.inl j) => finiteCascadeContinuationOldLeaf k.continuation
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U j).depth)
        (cavityGeneratedObservedRawChartEdge U j))
      (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U j).depth) U.tree i)
  | .inr (.inr _) => finiteCascadeContinuationOldLeaf k.continuation (.root U.tree) i

def cavityGeneratedObservedRawChartFreshLeaf
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree) :
    ObservationLeaf (cavityGeneratedObservedRawChartComponent U γ .single).tree :=
  match γ with
  | .inl i => finiteCascadeContinuationNewLeaf observationLinearTree (cavityGeneratedObservedRawChartFork U i)
      (observationLinearLeaf (cavityGeneratedObservedRawChartFork U i).depth)
  | .inr (.inl i) => finiteCascadeContinuationNewLeaf observationLinearTree
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        (cavityGeneratedObservedRawChartEdge U i))
      (observationLinearLeaf (nativeStreamingEdgeRefinedVertex
        (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        (cavityGeneratedObservedRawChartEdge U i)).depth)
  | .inr (.inr _) => finiteCascadeContinuationNewLeaf observationLinearTree (.root U.tree)
      (observationLinearLeaf U.depth)

def cavityGeneratedObservedRawChartCurrentLeaf
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree) (b : Bool) :
    ObservationLeaf (cavityGeneratedObservedRawChartComponent U γ .current).tree :=
  match γ with
  | .inl i => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree (cavityGeneratedObservedRawChartFork U i)
      (if b then Sum.inr (observationLinearLeaf (cavityGeneratedObservedRawChartFork U i).depth)
        else Sum.inl (observationLinearLeaf (cavityGeneratedObservedRawChartFork U i).depth))
  | .inr (.inl i) => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        (cavityGeneratedObservedRawChartEdge U i))
      (if b then Sum.inr (observationLinearLeaf (nativeStreamingEdgeRefinedVertex
        (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
        (cavityGeneratedObservedRawChartEdge U i)).depth)
        else Sum.inl (observationLinearLeaf (nativeStreamingEdgeRefinedVertex
          (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U i).depth)
          (cavityGeneratedObservedRawChartEdge U i)).depth))
  | .inr (.inr _) => finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree (.root U.tree)
      (if b then Sum.inr (observationLinearLeaf U.depth) else Sum.inl (observationLinearLeaf U.depth))

theorem cavityGeneratedObservedRawChartTerminalProject_old_leaf {S : Type}
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (i : ObservationLeaf U.tree)
    (σ : TerminalSpins S (cavityGeneratedObservedRawChartComponent U γ k).tree) :
    observationTerminalSpin U.tree i (cavityGeneratedObservedRawChartTerminalProject U γ k σ).1 =
      observationTerminalSpin _ (cavityGeneratedObservedRawChartOldLeaf U γ k i) σ := by
  rcases γ with j | (j | u)
  · exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ i σ
  · change observationTerminalSpin U.tree i (observationRefinementTerminalProject _ U.tree rfl _) = _
    rw [observationRefinementTerminalProject_leaf]
    exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ _ σ
  · exact nativeStreamingGeneratedVertexTerminalProjection_old_terminal_leaf k _ i σ

theorem cavityGeneratedObservedRawChartTerminalProject_fresh_leaf {S : Type}
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (σ : TerminalSpins S (cavityGeneratedObservedRawChartComponent U γ .single).tree) :
    (cavityGeneratedObservedRawChartTerminalProject U γ .single σ).2 =
      observationTerminalSpin _ (cavityGeneratedObservedRawChartFreshLeaf U γ) σ := by
  rcases γ with j | (j | u)
  all_goals exact nativeStreamingGeneratedVertexTerminalProjection_single_new_leaf _ σ

theorem cavityGeneratedObservedRawChartTerminalProject_current_leaf {S : Type}
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (σ : TerminalSpins S (cavityGeneratedObservedRawChartComponent U γ .current).tree) (b : Bool) :
    (if b then (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).2.2
      else (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).2.1) =
      observationTerminalSpin _ (cavityGeneratedObservedRawChartCurrentLeaf U γ b) σ := by
  rcases γ with j | (j | u)
  all_goals exact nativeStreamingGeneratedVertexTerminalProjection_current_new_leaf _ σ b

theorem cavityGeneratedObservedRawChartOldLeaves_commonClock
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (i j : ObservationLeaf U.tree) :
    (cavityGeneratedObservedRawChartComponent U γ k).clock
      (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
      (observationCommonLevel _ (cavityGeneratedObservedRawChartOldLeaf U γ k i)
        (cavityGeneratedObservedRawChartOldLeaf U γ k j)) = U.clock h (observationCommonLevel U.tree i j) := by
  rw [cavityGeneratedObservedRawChartComponent_clock U γ k h r hr]
  rcases γ with a | (a | u)
  · exact congrArg (U.clock h) (finiteCascadeContinuationOldLeaf_commonLevel k.continuation _ i j)
  · change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U a).depth r
      (observationCommonLevel _ (finiteCascadeContinuationOldLeaf k.continuation _ _)
        (finiteCascadeContinuationOldLeaf k.continuation _ _)) = _
    rw [finiteCascadeContinuationOldLeaf_commonLevel]
    change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U a).depth r
      (observationCommonLevel
        (observationRefineTree (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U a).depth) U.tree)
        (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U a).depth) U.tree i)
        (observationRefinementLeafEmbed (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U a).depth) U.tree j)) = _
    rw [observationRefinementLeafEmbed_commonLevel,nativeStreamingEdgeSchedule_refinement]
  · exact congrArg (U.clock h) (finiteCascadeContinuationOldLeaf_commonLevel k.continuation _ i j)

theorem cavityGeneratedObservedRawChartCurrentLeaves_commonClock
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r) :
    (cavityGeneratedObservedRawChartComponent U γ .current).clock
      (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
      (observationCommonLevel _ (cavityGeneratedObservedRawChartCurrentLeaf U γ false)
        (cavityGeneratedObservedRawChartCurrentLeaf U γ true)) =
      nativeStreamingOriginLevel (U.clock h) (cavityGeneratedObservedRawChartOrigin U γ r) := by
  rw [cavityGeneratedObservedRawChartComponent_clock U γ .current h r hr]
  rcases γ with a | (a | u)
  · change U.clock h (observationCommonLevel _ (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel]
    rfl
  · change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U a).depth r
      (observationCommonLevel _ (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel]
    change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U a).depth r
      (nativeStreamingEdgeRefinedVertex (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U a).depth)
        (cavityGeneratedObservedRawChartEdge U a)).depth = r
    exact nativeStreamingEdgeRefinedVertex_inserted_level _ _ _
  · change U.clock h (observationCommonLevel _ (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)
        (finiteCascadeContinuationNewLeaf nativeStreamingCurrentPairTree _ _)) = _
    rw [finiteCascadeContinuationNewLeaf_commonLevel]
    rfl

theorem cavityGeneratedObservedRawChartOldLeaf_injective
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) :
    Function.Injective (cavityGeneratedObservedRawChartOldLeaf U γ k) := by
  rcases γ with i | (i | u)
  · exact finiteCascadeContinuationOldLeaf_injective k.continuation _
  · exact (finiteCascadeContinuationOldLeaf_injective k.continuation _).comp
      (observationRefinementLeafEmbed_injective _ U.tree)
  · exact finiteCascadeContinuationOldLeaf_injective k.continuation _

theorem cavityGeneratedObservedRawChartOldLeaf_ne_fresh
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (i : ObservationLeaf U.tree) :
    cavityGeneratedObservedRawChartOldLeaf U γ .single i ≠ cavityGeneratedObservedRawChartFreshLeaf U γ := by
  rcases γ with v | (e | u)
  all_goals exact finiteCascadeContinuationOldNewLeaf_ne observationLinearTree _ _ _

theorem cavityGeneratedObservedRawChartCurrentLeaves_ne
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree) :
    cavityGeneratedObservedRawChartCurrentLeaf U γ false ≠ cavityGeneratedObservedRawChartCurrentLeaf U γ true := by
  rcases γ with v | (e | u)
  all_goals
    intro he
    have hn := (finiteCascadeContinuationNewLeaf_injective nativeStreamingCurrentPairTree _) he
    cases hn

theorem cavityGeneratedObservedRawChartOldFresh_commonClock
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r) (i : ObservationLeaf U.tree) :
    (cavityGeneratedObservedRawChartComponent U γ .single).clock
      (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
      (observationCommonLevel _ (cavityGeneratedObservedRawChartOldLeaf U γ .single i)
        (cavityGeneratedObservedRawChartFreshLeaf U γ)) =
      nativeStreamingOriginCommonClock (U.clock h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (cavityGeneratedObservedRawChartOrigin U γ r) := by
  rw [cavityGeneratedObservedRawChartComponent_clock U γ .single h r hr]
  rcases γ with v | (e | u)
  · exact congrArg (U.clock h) (finiteCascadeContinuationOldNewLeaf_commonLevel observationLinearTree _ i _)
  · change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U e).depth r
      (observationCommonLevel _ (finiteCascadeContinuationOldLeaf observationLinearTree _ _)
        (finiteCascadeContinuationNewLeaf observationLinearTree _ _)) = _
    rw [finiteCascadeContinuationOldNewLeaf_commonLevel]
    change nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U e).depth r
      (finiteCascadeCommonPathDepth
        (observationRefineTree (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U e).depth) U.tree)
        (observationLeafVertex _ (observationRefinementLeafEmbed _ U.tree i))
        (nativeStreamingEdgeRefinedVertex
          (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U e).depth)
          (cavityGeneratedObservedRawChartEdge U e))) = _
    rw [nativeStreamingRefinementLeafEmbed_vertex,←nativeStreamingSelected_one_slot_vertex]
    exact nativeStreamingEdgeOldLeaf_commonPathClock_eq_mark
      (nativeStreamingEdgeSubdivision (cavityGeneratedObservedRawChartEdge U e).depth) (U.clock h)
      (nativeStreamingEdgeSchedule (U.clock h) (cavityGeneratedObservedRawChartEdge U e).depth r)
      U.tree (fun j _ => nativeStreamingEdgeSchedule_refinement _ _ _ j) i _ 0
      (by simp [nativeStreamingEdgeSubdivision]) r
      (by simp only [Nat.add_zero,nativeStreamingEdgeSubdivision_depth,le_refl,if_true,
        nativeStreamingEdgeSchedule_inserted])
  · exact congrArg (U.clock h) (finiteCascadeContinuationOldNewLeaf_commonLevel observationLinearTree _ i _)

theorem cavityGeneratedObservedRawChartOldPair_defect
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (k : NativeStreamingGeneratedVertexKind) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (i j : ObservationLeaf U.tree)
    (σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedObservedRawChartComponent U γ k).tree) :
    cavitySpinOverlapDefect n (U.clock h (observationCommonLevel U.tree i j))
      (observationTerminalSpin U.tree i (cavityGeneratedObservedRawChartTerminalProject U γ k σ).1)
      (observationTerminalSpin U.tree j (cavityGeneratedObservedRawChartTerminalProject U γ k σ).1) =
    cavitySpinOverlapDefect n
      ((cavityGeneratedObservedRawChartComponent U γ k).clock
        (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
        (observationCommonLevel _ (cavityGeneratedObservedRawChartOldLeaf U γ k i)
          (cavityGeneratedObservedRawChartOldLeaf U γ k j)))
      (observationTerminalSpin _ (cavityGeneratedObservedRawChartOldLeaf U γ k i) σ)
      (observationTerminalSpin _ (cavityGeneratedObservedRawChartOldLeaf U γ k j) σ) := by
  rw [cavityGeneratedObservedRawChartOldLeaves_commonClock U γ k h r hr,
    cavityGeneratedObservedRawChartTerminalProject_old_leaf,
    cavityGeneratedObservedRawChartTerminalProject_old_leaf]

theorem cavityGeneratedObservedRawChartOriginalFreshTest_terminal
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (F : TerminalSpins (Configuration (n+1)) U.tree → ℝ) (i : ObservationLeaf U.tree)
    (σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedObservedRawChartComponent U γ .single).tree) :
    nativeStreamingOriginalFreshSpinTest U.tree F i
      (nativeStreamingOriginCommonClock (U.clock h) U.tree
        (.vertex (observationLeafVertex U.tree i)) (cavityGeneratedObservedRawChartOrigin U γ r))
      (cavityGeneratedObservedRawChartTerminalProject U γ .single σ) =
    F (cavityGeneratedObservedRawChartTerminalProject U γ .single σ).1 *
      cavitySpinOverlapDefect n
        ((cavityGeneratedObservedRawChartComponent U γ .single).clock
          (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
          (observationCommonLevel _ (cavityGeneratedObservedRawChartOldLeaf U γ .single i)
            (cavityGeneratedObservedRawChartFreshLeaf U γ)))
        (observationTerminalSpin _ (cavityGeneratedObservedRawChartOldLeaf U γ .single i) σ)
        (observationTerminalSpin _ (cavityGeneratedObservedRawChartFreshLeaf U γ) σ) := by
  unfold nativeStreamingOriginalFreshSpinTest
  rw [cavityGeneratedObservedRawChartOldFresh_commonClock U γ h r hr,
    cavityGeneratedObservedRawChartTerminalProject_old_leaf,
    cavityGeneratedObservedRawChartTerminalProject_fresh_leaf]

theorem cavityGeneratedObservedRawChartCurrentTest_terminal
    (U : CavityGeneratedObservedRawComponent m) (γ : CavityGeneratedObservedRawOriginChart U.tree)
    (h : CavityGeneratedHistory Paper.Overlap m) (r : Paper.Overlap)
    (hr : cavityGeneratedObservedRawChartCell U γ h r)
    (F : TerminalSpins (Configuration (n+1)) U.tree → ℝ)
    (σ : TerminalSpins (Configuration (n+1)) (cavityGeneratedObservedRawChartComponent U γ .current).tree) :
    nativeStreamingDefectSpinTest U.tree F
      (nativeStreamingOriginLevel (U.clock h) (cavityGeneratedObservedRawChartOrigin U γ r))
      (cavityGeneratedObservedRawChartTerminalProject U γ .current σ) =
    F (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).1 *
      cavitySpinOverlapDefect n
        ((cavityGeneratedObservedRawChartComponent U γ .current).clock
          (Fin.snoc h (cavityGeneratedObservedRawChartClock U γ h r))
          (observationCommonLevel _ (cavityGeneratedObservedRawChartCurrentLeaf U γ false)
            (cavityGeneratedObservedRawChartCurrentLeaf U γ true)))
        (observationTerminalSpin _ (cavityGeneratedObservedRawChartCurrentLeaf U γ false) σ)
        (observationTerminalSpin _ (cavityGeneratedObservedRawChartCurrentLeaf U γ true) σ) := by
  unfold nativeStreamingDefectSpinTest
  rw [cavityGeneratedObservedRawChartCurrentLeaves_commonClock U γ h r hr]
  change F (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).1 *
    cavitySpinOverlapDefect n _ (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).2.1
      (cavityGeneratedObservedRawChartTerminalProject U γ .current σ).2.2 = _
  have hf := cavityGeneratedObservedRawChartTerminalProject_current_leaf U γ σ false
  have ht := cavityGeneratedObservedRawChartTerminalProject_current_leaf U γ σ true
  simp only [Bool.false_eq_true, if_false, Bool.true_eq, if_true] at hf ht
  rw [hf,ht]

end QuantitativeFollowup
