module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedGeometry

@[expose] public section

/-! Antitone physical clocks turn a shared refined path into the earlier of
two selected times. Repeated times and diagonal marks require no exclusion. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

theorem nativeStreamingSelectedGeometry_commonPathDepth_self {j : ℕ}
    (T : FiniteTerminalGenealogy j) (v : FiniteCascadeRecordVertex T) :
    finiteCascadeCommonPathDepth T v v = v.depth := by
  induction v with
  | root T => cases T <;> rfl
  | child v ih => exact ih
  | left v ih => exact ih
  | right v ih => exact ih

@[reducible] def nativeStreamingSelectedCommonClock {A : Type*} [LinearOrder A]
    (c de df : ℕ) (r l qc : A) : A :=
  if c = de then (if c = df then min r l else r)
  else if c = df then l else qc

theorem nativeStreamingEdgeSelectedVertex_commonPathClock
    {A : Type*} [LinearOrder A] (d : ℕ → ℕ) (q Q : ℕ → A)
    (hQ : Antitone Q) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀ i ≤ j, Q (observationRefinementDepth d i) = q i)
    (e f : NativeStreamingEdge T) (p k : ℕ)
    (hp : p < d e.depth) (hk : k < d f.depth) :
    let c : ℕ := finiteCascadeCommonPathDepth T
      (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
    let r := Q (observationRefinementDepth d e.depth + p + 1)
    let l := Q (observationRefinementDepth d f.depth + k + 1)
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)) =
      nativeStreamingSelectedCommonClock c e.depth f.depth r l (q c) := by
  dsimp only [nativeStreamingSelectedCommonClock]
  rw [nativeStreamingEdgeSelectedVertex_commonPathDepth d T e f p k hp hk]
  simp only [nativeStreamingSelectedCommonDepth]
  by_cases he : finiteCascadeCommonPathDepth T
      (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f) = e.depth
  · by_cases hf : finiteCascadeCommonPathDepth T
        (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f) = f.depth
    · simp only [if_pos he, if_pos hf, hQ.map_max]
    · simp only [if_pos he, if_neg hf]
  · by_cases hf : finiteCascadeCommonPathDepth T
        (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f) = f.depth
    · simp only [if_neg he, if_pos hf]
    · simp only [if_neg he, if_neg hf]
      exact hlevels _ (finiteCascadeCommonPathDepth_le T _ _)

theorem nativeStreamingEdgeSelectedVertex_commonPathClock_eq_marks
    {A : Type*} [LinearOrder A] (d : ℕ → ℕ) (q Q : ℕ → A)
    (hQ : Antitone Q) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀ i ≤ j, Q (observationRefinementDepth d i) = q i)
    (e f : NativeStreamingEdge T) (p k : ℕ)
    (hp : p < d e.depth) (hk : k < d f.depth) (r l : A)
    (hr : Q (observationRefinementDepth d e.depth + p + 1) = r)
    (hl : Q (observationRefinementDepth d f.depth + k + 1) = l) :
    let c : ℕ := finiteCascadeCommonPathDepth T
      (nativeStreamingEdgeChildVertex e) (nativeStreamingEdgeChildVertex f)
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d f k)) =
      nativeStreamingSelectedCommonClock c e.depth f.depth r l (q c) := by
  simpa only [hr, hl] using
    nativeStreamingEdgeSelectedVertex_commonPathClock d q Q hQ T hlevels e f p k hp hk

theorem nativeStreamingEdgeSelectedVertex_sameEdge_commonPathClock
    {A : Type*} [LinearOrder A] (d : ℕ → ℕ) (q Q : ℕ → A)
    (hQ : Antitone Q) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hlevels : ∀ i ≤ j, Q (observationRefinementDepth d i) = q i)
    (e : NativeStreamingEdge T) (p k : ℕ)
    (hp : p < d e.depth) (hk : k < d e.depth) :
    Q (finiteCascadeCommonPathDepth (observationRefineTree d T)
      (nativeStreamingEdgeSelectedVertex d e p) (nativeStreamingEdgeSelectedVertex d e k)) =
      min (Q (observationRefinementDepth d e.depth + p + 1))
        (Q (observationRefinementDepth d e.depth + k + 1)) := by
  simpa only [nativeStreamingSelectedGeometry_commonPathDepth_self,
    nativeStreamingEdgeChildVertex_depth, nativeStreamingSelectedCommonClock, if_true] using
      nativeStreamingEdgeSelectedVertex_commonPathClock d q Q hQ T hlevels e e p k hp hk

end QuantitativeFollowup
