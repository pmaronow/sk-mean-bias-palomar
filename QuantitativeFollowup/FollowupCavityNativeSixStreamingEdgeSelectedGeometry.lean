module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedVertex
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement

@[expose] public section

/-! The two selected observations are genuine vertices of the refined tree.
Their common path is computed from the original lower edge vertices, including
two marks on one edge and coincident selections. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
attribute [local instance] Classical.propDecidable

@[reducible] def nativeStreamingEdgeChildVertex :
    {j : ℕ} → {T : FiniteTerminalGenealogy j} → NativeStreamingEdge T →
      FiniteCascadeRecordVertex T
  | _, _, .here T => .child (.root T)
  | _, _, .child e => .child (nativeStreamingEdgeChildVertex e)
  | _, _, .left e => .left (nativeStreamingEdgeChildVertex e)
  | _, _, .right e => .right (nativeStreamingEdgeChildVertex e)

theorem nativeStreamingEdgeChildVertex_depth {j : ℕ} {T : FiniteTerminalGenealogy j}
    (e : NativeStreamingEdge T) : (nativeStreamingEdgeChildVertex e).depth = e.depth := by
  induction e with
  | here T => rfl
  | child e ih => exact ih
  | left e ih => exact ih
  | right e ih => exact ih

theorem nativeStreamingSelectedGeometry_commonPathDepth_symm {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v w = finiteCascadeCommonPathDepth T w v := by
  induction T with
  | leaf => cases v; cases w; rfl
  | advance T ih =>
      cases v with
      | root => cases w <;> rfl
      | child v => cases w with
        | root => rfl
        | child w => exact ih v w
  | fork T U ihT ihU =>
      cases v with
      | root => cases w <;> rfl
      | left v => cases w with
        | root => rfl
        | left w => exact ihT v w
        | right w => rfl
      | right v => cases w with
        | root => rfl
        | left w => rfl
        | right w => exact ihU v w

private theorem nativeStreamingSelectedGeometry_root_left {j : ℕ}
    (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T (.root T) w = j := by
  cases T <;> cases w <;> rfl

private theorem nativeStreamingSelectedGeometry_root_right {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v (.root T) = j := by
  cases T <;> cases v <;> rfl

theorem nativeStreamingBlockSelectedVertexAt_commonPath_pad {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p : ℕ) (hp : p < d)
    (v : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth (.advance (observationTreePad T d))
      (nativeStreamingBlockSelectedVertexAt T d p)
      (.child (nativeStreamingPadVertexEmbed T d v)) = j + p + 1 := by
  induction d generalizing p with
  | zero => omega
  | succ d ih =>
      by_cases he : p = d
      · subst p
        simp only [nativeStreamingBlockSelectedVertexAt, if_true,
          nativeStreamingPadVertexEmbed, finiteCascadeCommonPathDepth]
        rfl
      · have hp' : p < d := by omega
        simp only [nativeStreamingBlockSelectedVertexAt, if_neg he,
          nativeStreamingPadVertexEmbed, finiteCascadeCommonPathDepth]
        exact ih p hp'

theorem nativeStreamingBlockSelectedVertexAt_commonPath {j : ℕ}
    (T : FiniteTerminalGenealogy j) (d p k : ℕ) (hp : p < d) (hk : k < d) :
    finiteCascadeCommonPathDepth (.advance (observationTreePad T d))
      (nativeStreamingBlockSelectedVertexAt T d p)
      (nativeStreamingBlockSelectedVertexAt T d k) = max (j + p + 1) (j + k + 1) := by
  induction d generalizing p k with
  | zero => omega
  | succ d ih =>
      by_cases he : p = d
      · subst p
        by_cases hf : k = d
        · subst k
          simp only [nativeStreamingBlockSelectedVertexAt, if_true,
            finiteCascadeCommonPathDepth, max_self]
          rfl
        · have hk' : k < d := by omega
          simp only [nativeStreamingBlockSelectedVertexAt, if_true, if_neg hf,
            finiteCascadeCommonPathDepth]
          change j + d + 1 = max (j + d + 1) (j + k + 1)
          exact (max_eq_left (by omega)).symm
      · have hp' : p < d := by omega
        by_cases hf : k = d
        · subst k
          simp only [nativeStreamingBlockSelectedVertexAt, if_true, if_neg he]
          change finiteCascadeCommonPathDepth (.advance (observationTreePad T d))
            (nativeStreamingBlockSelectedVertexAt T d p) (.root _) =
              max (j + p + 1) (j + d + 1)
          rw [nativeStreamingSelectedGeometry_root_right]
          change j + d + 1 = max (j + p + 1) (j + d + 1)
          exact (max_eq_right (by omega)).symm
        · have hk' : k < d := by omega
          simp only [nativeStreamingBlockSelectedVertexAt, if_neg he, if_neg hf,
            finiteCascadeCommonPathDepth]
          exact ih p k hp' hk'

@[reducible] def nativeStreamingSelectedCommonDepth (d : ℕ → ℕ)
    (c de df se sf : ℕ) : ℕ :=
  if c = de then (if c = df then max se sf else se)
  else if c = df then sf else observationRefinementDepth d c

theorem nativeStreamingEdgeSelectedVertex_commonPathDepth (d : ℕ → ℕ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (e f : NativeStreamingEdge T)
    (p k : ℕ) (hp : p < d e.depth) (hk : k < d f.depth) :
    let c : ℕ := finiteCascadeCommonPathDepth T
      (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
    let se : ℕ := observationRefinementDepth d e.depth + p + 1
    let sf : ℕ := observationRefinementDepth d f.depth + k + 1
    finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k) =
      nativeStreamingSelectedCommonDepth d c e.depth f.depth se sf := by
  dsimp only [nativeStreamingSelectedCommonDepth]
  induction T generalizing p k with
  | leaf => cases e
  | @advance j T ih =>
      cases e with
      | here =>
          cases f with
          | here =>
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingSelectedGeometry_root_left,
                if_true, nativeStreamingEdgeSelectedVertex, observationRefineTree]
              exact nativeStreamingBlockSelectedVertexAt_commonPath
                (observationRefineTree d T) (d j) p k hp hk
          | child f =>
              have hf : j ≠ f.depth := Ne.symm (Nat.ne_of_lt f.depth_lt)
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingSelectedGeometry_root_left,
                if_true, if_neg hf, nativeStreamingEdgeSelectedVertex, observationRefineTree]
              exact nativeStreamingBlockSelectedVertexAt_commonPath_pad
                (observationRefineTree d T) (d j) p hp (nativeStreamingEdgeSelectedVertex d f k)
      | child e =>
          cases f with
          | here =>
              have he : j ≠ e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingSelectedGeometry_root_right,
                if_neg he, if_true, nativeStreamingEdgeSelectedVertex, observationRefineTree]
              change finiteCascadeCommonPathDepth
                (.advance (observationTreePad (observationRefineTree d T) (d j)))
                (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j)
                  (nativeStreamingEdgeSelectedVertex d e p)))
                (nativeStreamingBlockSelectedVertexAt (observationRefineTree d T) (d j) k) =
                  observationRefinementDepth d j + k + 1
              rw [nativeStreamingSelectedGeometry_commonPathDepth_symm]
              exact nativeStreamingBlockSelectedVertexAt_commonPath_pad
                (observationRefineTree d T) (d j) k hk (nativeStreamingEdgeSelectedVertex d e p)
          | child f =>
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingEdgeSelectedVertex, observationRefineTree]
              rw [nativeStreamingPadVertexEmbed_commonPathDepth]
              exact ih e f p k hp hk
  | @fork j T U ihT ihU =>
      cases e with
      | left e =>
          cases f with
          | left f => exact ihT e f p k hp hk
          | right f =>
              have he : j ≠ e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
              have hf : j ≠ f.depth := Ne.symm (Nat.ne_of_lt f.depth_lt)
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingEdgeSelectedVertex,
                observationRefineTree, if_neg he, if_neg hf]
      | right e =>
          cases f with
          | left f =>
              have he : j ≠ e.depth := Ne.symm (Nat.ne_of_lt e.depth_lt)
              have hf : j ≠ f.depth := Ne.symm (Nat.ne_of_lt f.depth_lt)
              simp only [nativeStreamingEdgeChildVertex, NativeStreamingEdge.depth,
                finiteCascadeCommonPathDepth, nativeStreamingEdgeSelectedVertex,
                observationRefineTree, if_neg he, if_neg hf]
          | right f => exact ihU e f p k hp hk

end QuantitativeFollowup
