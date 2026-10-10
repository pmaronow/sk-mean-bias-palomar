module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgePairSelectedMarkLaw
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTwoBlockSelection

@[expose] public section

/-! Exact record-coordinate decompositions of a joint two-edge observation.
Every map preserves the entire original record, including the record in
branches without a selected edge. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S : Type}
set_option maxHeartbeats 1000000

 theorem nativeStreamingEdgePairSelection_here_here (d : ℕ → ℕ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.here T) (.here T) p k=
      (fun z=> (z.1,(z.2.1,(z.2.2.1,observationRefinementProject d T z.2.2.2)))) ∘
        nativeStreamingTwoBlockSelection (observationRefineTree d T) (d j) p k := by
  funext z
  dsimp only [nativeStreamingEdgePairSelection,nativeStreamingEdgeSelection,
    nativeStreamingTwoBlockSelection,Function.comp_apply]
  rfl

 theorem nativeStreamingEdgePairSelection_here_child (d : ℕ → ℕ) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (f : NativeStreamingEdge T) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.here T) (.child f) p k=
      (fun z=> (z.1,(z.2.2.1,(z.2.1,z.2.2.2)))) ∘
        Prod.map id (Prod.map id (nativeStreamingEdgeSelection d f k)) ∘
          nativeStreamingBlockSelectionAt (observationRefineTree d T) (d j) p := by
  funext z
  dsimp only [nativeStreamingEdgePairSelection,nativeStreamingEdgeSelection,
    Function.comp_apply,Prod.map]
  have hs := nativeStreamingBlockSelectionAt_snd (E:=E) (S:=S)
    (observationRefineTree d T) (d j) p z
  rw [congrArg Prod.fst hs,congrArg Prod.snd hs,nativeStreamingEdgeSelection_snd]
  rfl

 theorem nativeStreamingEdgePairSelection_child_here (d : ℕ → ℕ) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.child e) (.here T) p k=
      (fun z=> (z.2.2.1,(z.1,(z.2.1,z.2.2.2)))) ∘
        Prod.map id (Prod.map id (nativeStreamingEdgeSelection d e p)) ∘
          nativeStreamingBlockSelectionAt (observationRefineTree d T) (d j) k := by
  funext z
  dsimp only [nativeStreamingEdgePairSelection,nativeStreamingEdgeSelection,
    Function.comp_apply,Prod.map]
  have hs := nativeStreamingBlockSelectionAt_snd (E:=E) (S:=S)
    (observationRefineTree d T) (d j) k z
  rw [congrArg Prod.fst hs,congrArg Prod.snd hs,nativeStreamingEdgeSelection_snd]
  rfl

 theorem nativeStreamingEdgePairSelection_child_child (d : ℕ → ℕ) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge T) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.child e) (.child f) p k=
      (fun z=> (z.2.1,(z.2.2.1,(z.1,z.2.2.2)))) ∘
        Prod.map id (nativeStreamingEdgePairSelection d e f p k) ∘
          observationBlockCollapse (observationRefineTree d T) (d j) := by
  funext z
  rfl

 theorem nativeStreamingEdgePairSelection_left_left (d : ℕ → ℕ) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge T) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d
      (@NativeStreamingEdge.left j T U e) (.left f) p k=
      (fun z=> (z.1.1,(z.1.2.1,(z.1.2.2,z.2)))) ∘
        Prod.map (nativeStreamingEdgePairSelection d e f p k)
          (observationRefinementProject d U) := by
  funext z
  rfl

 theorem nativeStreamingEdgePairSelection_right_right (d : ℕ → ℕ) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (e f : NativeStreamingEdge U) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d
      (@NativeStreamingEdge.right j T U e) (.right f) p k=
      (fun z=> (z.2.1,(z.2.2.1,(z.1,z.2.2.2)))) ∘
        Prod.map (observationRefinementProject d T)
          (nativeStreamingEdgePairSelection d e f p k) := by
  funext z
  rfl

 theorem nativeStreamingEdgePairSelection_left_right (d : ℕ → ℕ) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (f : NativeStreamingEdge U) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.left e) (.right f) p k=
      (fun z=> (z.1.1,(z.2.1,(z.1.2,z.2.2)))) ∘
        Prod.map (nativeStreamingEdgeSelection d e p) (nativeStreamingEdgeSelection d f k) := by
  funext z
  dsimp only [nativeStreamingEdgePairSelection,nativeStreamingEdgeSelection,
    Function.comp_apply,Prod.map]
  rw [nativeStreamingEdgeSelection_snd,nativeStreamingEdgeSelection_snd]
  rfl

 theorem nativeStreamingEdgePairSelection_right_left (d : ℕ → ℕ) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (e : NativeStreamingEdge U)
    (f : NativeStreamingEdge T) (p k : ℕ) :
    nativeStreamingEdgePairSelection (E:=E) (S:=S) d (.right e) (.left f) p k=
      (fun z=> (z.2.1,(z.1.1,(z.1.2,z.2.2)))) ∘
        Prod.map (nativeStreamingEdgeSelection d f k) (nativeStreamingEdgeSelection d e p) := by
  funext z
  dsimp only [nativeStreamingEdgePairSelection,nativeStreamingEdgeSelection,
    Function.comp_apply,Prod.map]
  rw [nativeStreamingEdgeSelection_snd,nativeStreamingEdgeSelection_snd]
  rfl

end QuantitativeFollowup
