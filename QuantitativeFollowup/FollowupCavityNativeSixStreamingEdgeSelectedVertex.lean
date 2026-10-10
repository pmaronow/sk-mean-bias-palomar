module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelection

@[expose] public section

/-! The state retained by the selective edge projection is the field of
an actual vertex in the refined tree.  Its exact observation index is
proved, so conditional terminal marks use the same native restart kernel. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S : Type}
set_option maxHeartbeats 1000000

@[reducible] def nativeStreamingBlockSelectedVertexAt {j : ℕ}
    (T : FiniteTerminalGenealogy j) : (d p : ℕ) →
      FiniteCascadeRecordVertex (.advance (observationTreePad T d))
  | 0, _ => .child (.root T)
  | d+1, p => if p=d then .child (.root (.advance (observationTreePad T d)))
      else .child (nativeStreamingBlockSelectedVertexAt T d p)

theorem nativeStreamingBlockSelectedVertexAt_depth {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) (hp : p<d) :
    (nativeStreamingBlockSelectedVertexAt T d p).depth=j+p+1 := by
  induction d generalizing p with
  | zero => omega
  | succ d ih =>
      by_cases he:p=d
      · subst p
        simp only [nativeStreamingBlockSelectedVertexAt]
        rfl
      · have hp':p<d:=by omega
        simp only [nativeStreamingBlockSelectedVertexAt,if_neg he]
        exact ih p hp'

theorem nativeStreamingBlockSelectedVertexAt_state {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) (H : E)
    (z : Records E S (.advance (observationTreePad T d))) :
    nativeStreamingVertexState (nativeStreamingBlockSelectedVertexAt T d p) H z=
      (nativeStreamingBlockSelectionAt T d p z).1 := by
  induction d generalizing p H with
  | zero => rfl
  | succ d ih =>
      by_cases he:p=d
      · simp only [nativeStreamingBlockSelectedVertexAt,nativeStreamingBlockSelectionAt,if_pos he]
        rfl
      · simp only [nativeStreamingBlockSelectedVertexAt,nativeStreamingBlockSelectionAt,if_neg he]
        exact ih p z.1 z.2

@[reducible] def nativeStreamingEdgeSelectedVertex (d : ℕ → ℕ) :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → NativeStreamingEdge T → (p : ℕ) →
      FiniteCascadeRecordVertex (observationRefineTree d T)
  | _, _, @NativeStreamingEdge.here j T, p =>
      nativeStreamingBlockSelectedVertexAt (observationRefineTree d T) (d j) p
  | _, _, @NativeStreamingEdge.child j T e, p =>
      .child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
        (nativeStreamingEdgeSelectedVertex d e p))
  | _, _, .left e, p => .left (nativeStreamingEdgeSelectedVertex d e p)
  | _, _, .right e, p => .right (nativeStreamingEdgeSelectedVertex d e p)

theorem nativeStreamingEdgeSelectedVertex_depth (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    (nativeStreamingEdgeSelectedVertex d e p).depth=observationRefinementDepth d e.depth+p+1 := by
  induction e with
  | here T => exact nativeStreamingBlockSelectedVertexAt_depth _ _ p hp
  | child e ih =>
      change (nativeStreamingPadVertexEmbed _ _ _).depth=_
      rw [nativeStreamingPadVertexEmbed_depth]
      exact ih hp
  | left e ih => exact ih hp
  | right e ih => exact ih hp

theorem nativeStreamingEdgeSelectedVertex_state (d : ℕ → ℕ)
    {j : ℕ} {T : FiniteTerminalGenealogy j} (e : NativeStreamingEdge T)
    (p : ℕ) (H : E) (z : Records E S (observationRefineTree d T)) :
    nativeStreamingVertexState (nativeStreamingEdgeSelectedVertex d e p) H z=
      (nativeStreamingEdgeSelection d e p z).1 := by
  induction e generalizing H with
  | here T => exact nativeStreamingBlockSelectedVertexAt_state _ _ p H z
  | @child j T e ih =>
      change nativeStreamingVertexState (nativeStreamingPadVertexEmbed _ (d j) _) z.1 z.2=_
      rw [nativeStreamingPadVertexEmbed_state,nativeStreamingPadStateProject_eq_block]
      exact ih (observationBlockCollapse _ _ z).1 (observationBlockCollapse _ _ z).2
  | left e ih => exact ih H z.1
  | right e ih => exact ih H z.2

end QuantitativeFollowup
