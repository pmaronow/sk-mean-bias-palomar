module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsClocks
public import FourPapersCommon.FiniteObservationEndpointPadding

@[expose] public section

/-! The genuine unary terminal lift and outer initial observation put every
old vertex in the interior. Old terminal spins and fields have explicit
projections, and their chosen common ancestor clocks are retained. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m J : ℕ}

theorem nativeStreamingGeneratedTerminalUnaryLift_constructed
    {labels refined : ℕ → CavityGeneratedClockLabel m}
    (T : FiniteTerminalGenealogy J) (hT : CavityGeneratedGenealogyConstruction labels T)
    (hc : ∀j, j ≤ J → refined (j+1)=labels j) :
    CavityGeneratedGenealogyConstruction refined (observationTerminalUnaryLift T) := by
  induction T with
  | leaf => exact .advance (.linear 0)
  | @advance j T ih =>
      apply CavityGeneratedGenealogyConstruction.advance
      apply ih
      · apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
        intro b e hbe
        exact hT.pair_clock_labels b e hbe
      · exact fun p hp => hc p (by omega)
  | @fork j T U ihT ihU =>
      obtain ⟨i,hi⟩ := hT.pair_clock_labels (Sum.inl (cavityGeneratedChosenLeaf T))
        (Sum.inr (cavityGeneratedChosenLeaf U)) (by intro he; cases he)
      change labels j=.mark i at hi
      apply CavityGeneratedGenealogyConstruction.fork i ((hc j le_rfl).trans hi)
      · apply ihT
        · apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
          intro b e hbe
          exact hT.pair_clock_labels (Sum.inl b) (Sum.inl e) (fun he => hbe (Sum.inl.inj he))
        · exact hc
      · apply ihU
        · apply CavityGeneratedGenealogyConstruction.of_pair_clock_labels
          intro b e hbe
          exact hT.pair_clock_labels (Sum.inr b) (Sum.inr e) (fun he => hbe (Sum.inr.inj he))
        · exact hc

def nativeStreamingGeneratedEndpointComponent (W : CavityGeneratedConstructedComponent m) :
    CavityGeneratedConstructedComponent m where
  depth := W.depth+2
  tree := .advance (observationTerminalUnaryLift W.tree)
  label := nativeStreamingGeneratedEndpointLabels W
  terminal_label := nativeStreamingGeneratedEndpointLabels_terminal W
  initial_label := nativeStreamingGeneratedEndpointLabels_initial W
  construction := .advance (nativeStreamingGeneratedTerminalUnaryLift_constructed W.tree W.construction
    (fun j _ => nativeStreamingGeneratedEndpointLabels_global_succ W j))

theorem nativeStreamingGeneratedEndpointComponent_clock
    (W : CavityGeneratedConstructedComponent m) (h : CavityGeneratedHistory Paper.Overlap m) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h =
      nativeStreamingGeneratedEndpointClock W h := rfl

@[reducible] def nativeStreamingEndpointLiftVertex : {j : ℕ} → {T : FiniteTerminalGenealogy j} →
    FiniteCascadeRecordVertex T → FiniteCascadeRecordVertex (observationTerminalUnaryLift T)
  | _, _, .root T => .root (observationTerminalUnaryLift T)
  | _, _, .child v => .child (nativeStreamingEndpointLiftVertex v)
  | _, _, .left v => .left (nativeStreamingEndpointLiftVertex v)
  | _, _, .right v => .right (nativeStreamingEndpointLiftVertex v)

theorem nativeStreamingEndpointLiftVertex_depth {T : FiniteTerminalGenealogy J}
    (v : FiniteCascadeRecordVertex T) : (nativeStreamingEndpointLiftVertex v).depth=v.depth+1 := by
  induction v with
  | root T => rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

@[reducible] def nativeStreamingGeneratedEndpointVertex
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree) :
    FiniteCascadeRecordVertex (nativeStreamingGeneratedEndpointComponent W).tree :=
  .child (nativeStreamingEndpointLiftVertex v)

theorem nativeStreamingGeneratedEndpointVertex_depth
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree) :
    (nativeStreamingGeneratedEndpointVertex W v).depth=v.depth+1 :=
  nativeStreamingEndpointLiftVertex_depth v

theorem nativeStreamingGeneratedEndpointVertex_interior
    (W : CavityGeneratedConstructedComponent m) (v : FiniteCascadeRecordVertex W.tree) :
    0 < (nativeStreamingGeneratedEndpointVertex W v).depth ∧
      (nativeStreamingGeneratedEndpointVertex W v).depth < (nativeStreamingGeneratedEndpointComponent W).depth := by
  rw [nativeStreamingGeneratedEndpointVertex_depth]
  have hv := v.depth_le
  change 0 < v.depth+1 ∧ v.depth+1 < W.depth+2
  omega

@[reducible] def nativeStreamingEndpointLiftLeaf : {j : ℕ} → (T : FiniteTerminalGenealogy j) →
    ObservationLeaf T → ObservationLeaf (observationTerminalUnaryLift T)
  | _, .leaf => id
  | _, .advance T => nativeStreamingEndpointLiftLeaf T
  | _, .fork T U => Sum.map (nativeStreamingEndpointLiftLeaf T) (nativeStreamingEndpointLiftLeaf U)

@[reducible] def nativeStreamingEndpointTerminalProject {S : Type} : {j : ℕ} →
    (T : FiniteTerminalGenealogy j) → TerminalSpins S (observationTerminalUnaryLift T) → TerminalSpins S T
  | _, .leaf => id
  | _, .advance T => nativeStreamingEndpointTerminalProject T
  | _, .fork T U => Prod.map (nativeStreamingEndpointTerminalProject T) (nativeStreamingEndpointTerminalProject U)

theorem nativeStreamingEndpointTerminalProject_record {E S : Type}
    (T : FiniteTerminalGenealogy J) (z : Records E S (observationTerminalUnaryLift T)) :
    nativeStreamingEndpointTerminalProject T (finiteCascadeRecordTerminalSpins _ z) =
      finiteCascadeRecordTerminalSpins T (observationTerminalUnaryProject T z) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih z.2
  | fork T U ihT ihU => exact Prod.ext (ihT z.1) (ihU z.2)

theorem nativeStreamingEndpointTerminalProject_leaf {S : Type}
    (T : FiniteTerminalGenealogy J) (i : ObservationLeaf T)
    (σ : TerminalSpins S (observationTerminalUnaryLift T)) :
    observationTerminalSpin T i (nativeStreamingEndpointTerminalProject T σ) =
      observationTerminalSpin _ (nativeStreamingEndpointLiftLeaf T i) σ := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih i σ
  | fork T U ihT ihU => cases i with
    | inl i => exact ihT i σ.1
    | inr i => exact ihU i σ.2

theorem nativeStreamingEndpointLiftVertex_state {E S : Type}
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T)
    (x : E) (z : Records E S (observationTerminalUnaryLift T)) :
    nativeStreamingVertexState (nativeStreamingEndpointLiftVertex v) x z =
      nativeStreamingVertexState v x (observationTerminalUnaryProject T z) := by
  induction v generalizing x with
  | root T => rfl
  | child v ih => exact ih z.1 z.2
  | left v ih => exact ih x z.1
  | right v ih => exact ih x z.2

theorem nativeStreamingEndpointLiftLeaf_vertex_commonDepth
    {T : FiniteTerminalGenealogy J} (v : FiniteCascadeRecordVertex T) (i : ObservationLeaf T) :
    finiteCascadeCommonPathDepth (observationTerminalUnaryLift T)
      (observationLeafVertex _ (nativeStreamingEndpointLiftLeaf T i)) (nativeStreamingEndpointLiftVertex v) =
        finiteCascadeCommonPathDepth T (observationLeafVertex T i) v + 1 := by
  induction v with
  | root T => simp only [nativeStreamingEndpointLiftVertex,finiteCascadeCommonPathDepth_root_right]
  | child v ih => exact ih i
  | left v ih => cases i with
    | inl i => exact ih i
    | inr i => rfl
  | right v ih => cases i with
    | inl i => rfl
    | inr i => exact ih i

end QuantitativeFollowup
