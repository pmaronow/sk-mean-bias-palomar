module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCharges
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingVertexRefinement
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingEdgeSelectedVertex

@[expose] public section

/-! Exact vertex-charge regrouping under observation subdivision. Every
padding edge is retained, even when its physical clock times coincide.
Only genuine forks contribute the original branch charges. -/
noncomputable section
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
open scoped BigOperators
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingRefinementVertexEmbed_root (d : ℕ → ℕ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) :
    nativeStreamingRefinementVertexEmbed d T (.root T) =
      .root (observationRefineTree d T) := by
  cases T <;> rfl

theorem nativeStreamingVertexBranchSum_pad (b : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (k : ℕ)
    (φ : FiniteCascadeRecordVertex (observationTreePad T k) → ℝ) :
    nativeStreamingVertexBranchSum b (observationTreePad T k) φ =
      nativeStreamingVertexBranchSum b T (fun v => φ (nativeStreamingPadVertexEmbed T k v)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      exact ih (fun v => φ (.child v))

theorem nativeStreamingVertexEdgeSum_pad_block (b : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j) (k : ℕ)
    (Φ : FiniteCascadeRecordVertex (.advance (observationTreePad T k)) → ℝ) :
    nativeStreamingVertexEdgeSum b (observationTreePad T k) (fun v => Φ (.child v)) =
      nativeStreamingVertexEdgeSum b T
        (fun v => Φ (.child (nativeStreamingPadVertexEmbed T k v))) +
      ∑p ∈ Finset.range k, (b (j+p)-b (j+p+1)) *
        Φ (nativeStreamingBlockSelectedVertexAt T k p) := by
  induction k with
  | zero => simp only [observationTreePad, nativeStreamingPadVertexEmbed,
      Finset.range_zero, Finset.sum_empty, add_zero]
  | succ k ih =>
      change nativeStreamingVertexEdgeSum b (observationTreePad T k)
          (fun v => Φ (.child (.child v))) +
        (b (j+k)-b (j+k+1))*Φ (.child (.root (observationTreePad T (k+1)))) = _
      rw [ih (fun v => Φ (.child v)), Finset.sum_range_succ]
      have hsum : (∑p ∈ Finset.range k, (b (j+p)-b (j+p+1)) *
          Φ (.child (nativeStreamingBlockSelectedVertexAt T k p))) =
        ∑p ∈ Finset.range k, (b (j+p)-b (j+p+1)) *
          Φ (nativeStreamingBlockSelectedVertexAt T (k+1) p) := by
        apply Finset.sum_congr rfl
        intro p hp
        have hpk : p ≠ k := (Finset.mem_range.mp hp).ne
        simp only [nativeStreamingBlockSelectedVertexAt, if_neg hpk]
      rw [hsum]
      simp only [nativeStreamingPadVertexEmbed, nativeStreamingBlockSelectedVertexAt,
        ite_true]
      ring

@[reducible] def nativeStreamingRefinedVertexEdgeSum (d : ℕ → ℕ) (b : ℕ → ℝ) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      (FiniteCascadeRecordVertex (observationRefineTree d T) → ℝ) → ℝ
  | _, .leaf, Φ => (1-b 0)*Φ (.root .leaf)
  | _, @FiniteTerminalGenealogy.advance j T, Φ =>
      nativeStreamingRefinedVertexEdgeSum d b T (fun v =>
        Φ (.child (nativeStreamingPadVertexEmbed (observationRefineTree d T) (d j) v))) +
      (∑p ∈ Finset.range (d j),
        (b (observationRefinementDepth d j+p)-b (observationRefinementDepth d j+p+1)) *
          Φ (nativeStreamingEdgeSelectedVertex d (NativeStreamingEdge.here T) p)) +
      (b (observationRefinementDepth d j+d j)-b (observationRefinementDepth d (j+1))) *
        Φ (.root (observationRefineTree d (.advance T)))
  | _, .fork T U, Φ =>
      nativeStreamingRefinedVertexEdgeSum d b T (fun v => Φ (.left v)) +
        nativeStreamingRefinedVertexEdgeSum d b U (fun v => Φ (.right v))

theorem nativeStreamingVertexEdgeSum_refinement (d : ℕ → ℕ) (b : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j)
    (Φ : FiniteCascadeRecordVertex (observationRefineTree d T) → ℝ) :
    nativeStreamingVertexEdgeSum b (observationRefineTree d T) Φ =
      nativeStreamingRefinedVertexEdgeSum d b T Φ := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      change nativeStreamingVertexEdgeSum b (observationTreePad (observationRefineTree d T) (d j))
          (fun v => Φ (.child v)) +
        (b (observationRefinementDepth d j+d j)-b (observationRefinementDepth d (j+1))) *
          Φ (.root (observationRefineTree d (.advance T))) = _
      rw [nativeStreamingVertexEdgeSum_pad_block]
      rw [ih]
  | fork T U ihT ihU =>
      exact congrArg₂ (·+·) (ihT (fun v => Φ (.left v))) (ihU (fun v => Φ (.right v)))

theorem nativeStreamingVertexBranchSum_refinement (d : ℕ → ℕ) (b : ℕ → ℝ) {j : ℕ}
    (T : FiniteTerminalGenealogy j)
    (Φ : FiniteCascadeRecordVertex (observationRefineTree d T) → ℝ) :
    nativeStreamingVertexBranchSum b (observationRefineTree d T) Φ =
      nativeStreamingVertexBranchSum (fun r => b (observationRefinementDepth d r)) T
        (fun v => Φ (nativeStreamingRefinementVertexEmbed d T v)) := by
  induction T with
  | leaf => rfl
  | @advance j T ih =>
      change nativeStreamingVertexBranchSum b (observationTreePad (observationRefineTree d T) (d j))
        (fun v => Φ (.child v)) = _
      rw [nativeStreamingVertexBranchSum_pad]
      exact ih (fun v => Φ (.child (nativeStreamingPadVertexEmbed
        (observationRefineTree d T) (d j) v)))
  | @fork j T U ihT ihU =>
      change _ + _ + b (observationRefinementDepth d j)*Φ (.root _) = _
      rw [ihT, ihU]
      rfl

theorem nativeStreamingVertexChargeSum_refinement (d : ℕ → ℕ) (b : ℕ → ℝ)
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ : FiniteCascadeRecordVertex (observationRefineTree d T) → ℝ)
    (hΦ : nativeStreamingRootCoherent (observationRefineTree d T) Φ) :
    nativeStreamingVertexChargeSum b s (observationRefineTree d T) Φ =
      nativeStreamingRefinedVertexEdgeSum d b T Φ +
        nativeStreamingVertexBranchSum (fun r => b (observationRefinementDepth d r)) T
          (fun v => Φ (nativeStreamingRefinementVertexEmbed d T v)) +
        (b (observationRefinementDepth d j)-s) *
          Φ (nativeStreamingRefinementVertexEmbed d T (.root T)) := by
  rw [nativeStreamingVertexChargeSum_eq_edges_branches b s _ Φ hΦ,
    nativeStreamingVertexEdgeSum_refinement, nativeStreamingVertexBranchSum_refinement,
    nativeStreamingRefinementVertexEmbed_root]

end QuantitativeFollowup
