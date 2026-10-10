module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometryClock

@[expose] public section

/-! An original retained vertex and an inserted edge observation share
the actual selected depth on the same ancestral path, and the refined
original common depth otherwise. Repeated clocks remain unrestricted. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
attribute [local instance] Classical.propDecidable

@[reducible] def nativeStreamingOldSelectedCommonDepth (d : ℕ → ℕ)
    (c de p : ℕ) : ℕ :=
  if c=de then observationRefinementDepth d de+p+1 else observationRefinementDepth d c

@[reducible] def nativeStreamingOldSelectedCommonClock {A : Type*}
    (c de : ℕ) (r qc : A) : A := if c=de then r else qc

private theorem nativeStreamingOldVertex_root_left {j : ℕ}
    (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T (.root T) w=j := by
  cases T <;> cases w <;> rfl

private theorem nativeStreamingOldVertex_root_right {j : ℕ}
    (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T w (.root T)=j := by
  cases T <;> cases w <;> rfl

theorem nativeStreamingEdgeOldVertex_commonPathDepth (d : ℕ → ℕ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T)
    (e : NativeStreamingEdge T) (p : ℕ) (hp : p<d e.depth) :
    let c : ℕ := finiteCascadeCommonPathDepth T w (nativeStreamingEdgeChildVertex e)
    finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T w) (nativeStreamingEdgeSelectedVertex d e p)=
      nativeStreamingOldSelectedCommonDepth d c e.depth p := by
  dsimp only [nativeStreamingOldSelectedCommonDepth]
  induction T generalizing p with
  | leaf => cases e
  | @advance j T ih =>
      cases w with
      | root =>
          have he : j+1≠e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
          change finiteCascadeCommonPathDepth (observationRefineTree d T.advance)
            (.root _) (nativeStreamingEdgeSelectedVertex d e p) =
            if j+1=e.depth then _ else observationRefinementDepth d (j+1)
          rw [nativeStreamingOldVertex_root_left, if_neg he]
      | child w =>
          cases e with
          | here =>
              change finiteCascadeCommonPathDepth
                (.advance (observationTreePad (observationRefineTree d T) (d j)))
                (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
                  (nativeStreamingRefinementVertexEmbed d T w)))
                (nativeStreamingBlockSelectedVertexAt (observationRefineTree d T) (d j) p) =
                if finiteCascadeCommonPathDepth T w (.root T)=j then
                  observationRefinementDepth d j+p+1 else _
              rw [nativeStreamingOldVertex_root_right, if_pos rfl,
                nativeStreamingSelectedGeometry_commonPathDepth_symm]
              exact nativeStreamingBlockSelectedVertexAt_commonPath_pad
                (observationRefineTree d T) (d j) p hp (nativeStreamingRefinementVertexEmbed d T w)
          | child e =>
              change finiteCascadeCommonPathDepth
                (observationTreePad (observationRefineTree d T) (d j))
                (nativeStreamingPadVertexEmbed _ _ (nativeStreamingRefinementVertexEmbed d T w))
                (nativeStreamingPadVertexEmbed _ _ (nativeStreamingEdgeSelectedVertex d e p)) = _
              rw [nativeStreamingPadVertexEmbed_commonPathDepth]
              exact ih w e p hp
  | @fork j T U ihT ihU =>
      cases w with
      | root =>
          have he : j≠e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
          change finiteCascadeCommonPathDepth (observationRefineTree d (T.fork U))
            (.root _) (nativeStreamingEdgeSelectedVertex d e p) =
            if j=e.depth then _ else observationRefinementDepth d j
          rw [nativeStreamingOldVertex_root_left, if_neg he]
      | left w =>
          cases e with
          | left e => exact ihT w e p hp
          | right e =>
              have he : j≠e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
              change observationRefinementDepth d j =
                if j=e.depth then _ else observationRefinementDepth d j
              rw [if_neg he]
      | right w =>
          cases e with
          | left e =>
              have he : j≠e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
              change observationRefinementDepth d j =
                if j=e.depth then _ else observationRefinementDepth d j
              rw [if_neg he]
          | right e => exact ihU w e p hp

theorem nativeStreamingEdgeOldVertex_commonPathClock {A : Type*}
    (d : ℕ → ℕ) (q Q : ℕ → A) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀i≤j,Q (observationRefinementDepth d i)=q i)
    (w : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) :
    let c : ℕ := finiteCascadeCommonPathDepth T w (nativeStreamingEdgeChildVertex e)
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T w) (nativeStreamingEdgeSelectedVertex d e p))=
      nativeStreamingOldSelectedCommonClock c e.depth
        (Q (observationRefinementDepth d e.depth+p+1)) (q c) := by
  dsimp only [nativeStreamingOldSelectedCommonClock]
  rw [nativeStreamingEdgeOldVertex_commonPathDepth d T w e p hp]
  simp only [nativeStreamingOldSelectedCommonDepth]
  split_ifs
  · rfl
  · exact hlevels _ (finiteCascadeCommonPathDepth_le T _ _)

theorem nativeStreamingEdgeOldVertex_commonPathClock_eq_mark {A : Type*}
    (d : ℕ → ℕ) (q Q : ℕ → A) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀i≤j,Q (observationRefinementDepth d i)=q i)
    (w : FiniteCascadeRecordVertex T) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (r : A)
    (hr : Q (observationRefinementDepth d e.depth+p+1)=r) :
    let c : ℕ := finiteCascadeCommonPathDepth T w (nativeStreamingEdgeChildVertex e)
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T w) (nativeStreamingEdgeSelectedVertex d e p))=
      nativeStreamingOldSelectedCommonClock c e.depth r (q c) := by
  simpa only [hr] using nativeStreamingEdgeOldVertex_commonPathClock d q Q T hlevels w e p hp

theorem nativeStreamingEdgeOldLeaf_commonPathClock_eq_mark {A : Type*}
    (d : ℕ → ℕ) (q Q : ℕ → A) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀i≤j,Q (observationRefinementDepth d i)=q i)
    (i : ObservationLeaf T) (e : NativeStreamingEdge T)
    (p : ℕ) (hp : p<d e.depth) (r : A)
    (hr : Q (observationRefinementDepth d e.depth+p+1)=r) :
    let c : ℕ := finiteCascadeCommonPathDepth T (observationLeafVertex T i)
      (nativeStreamingEdgeChildVertex e)
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingRefinementVertexEmbed d T (observationLeafVertex T i))
      (nativeStreamingEdgeSelectedVertex d e p))=
        nativeStreamingOldSelectedCommonClock c e.depth r (q c) :=
  nativeStreamingEdgeOldVertex_commonPathClock_eq_mark d q Q T hlevels
    (observationLeafVertex T i) e p hp r hr

end QuantitativeFollowup
