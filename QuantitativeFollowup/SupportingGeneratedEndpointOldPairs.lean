module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedEndpointVertexPatternsMoments

@[expose] public section

/-! Unary endpoint padding preserves every old pair at its physical common
clock. A diagonal pair keeps common level zero, while the old positive
branch levels move one slot inward. The two endpoint clock equations
therefore preserve both cases. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem nativeStreamingEndpointLiftLeaf_commonClock
    {A : Type*} {J : ℕ} (T : FiniteTerminalGenealogy J)
    (q Q : ℕ → A) (hzero : Q 0 = q 0) (hsucc : ∀ j, Q (j+1) = q j)
    (i k : ObservationLeaf T) :
    Q (observationCommonLevel (observationTerminalUnaryLift T)
      (nativeStreamingEndpointLiftLeaf T i) (nativeStreamingEndpointLiftLeaf T k)) =
      q (observationCommonLevel T i k) := by
  induction T with
  | leaf => exact hzero
  | advance T ih => exact ih i k
  | @fork j T U ihT ihU =>
      cases i with
      | inl i => cases k with
        | inl k => exact ihT i k
        | inr k => exact hsucc j
      | inr i => cases k with
        | inl k => exact hsucc j
        | inr k => exact ihU i k

theorem nativeStreamingGeneratedEndpointOldLeaves_commonClock
    (W : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (i k : ObservationLeaf W.tree) :
    nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h
      (observationCommonLevel (nativeStreamingGeneratedEndpointComponent W).tree
        (nativeStreamingGeneratedEndpointLeaf W i) (nativeStreamingGeneratedEndpointLeaf W k)) =
      nativeStreamingGeneratedComponentClock W h (observationCommonLevel W.tree i k) := by
  change nativeStreamingGeneratedEndpointClock W h
    (observationCommonLevel (observationTerminalUnaryLift W.tree)
      (nativeStreamingEndpointLiftLeaf W.tree i) (nativeStreamingEndpointLiftLeaf W.tree k)) = _
  exact nativeStreamingEndpointLiftLeaf_commonClock W.tree
    (nativeStreamingGeneratedComponentClock W h) (nativeStreamingGeneratedEndpointClock W h)
    ((nativeStreamingGeneratedEndpointClock_zero W h).trans
      (nativeStreamingGeneratedComponentClock_terminal W h).symm)
    (nativeStreamingGeneratedEndpointClock_succ W h) i k

theorem nativeStreamingGeneratedEndpointOldPair_defect
    (W : CavityGeneratedConstructedComponent m)
    (h : CavityGeneratedHistory Paper.Overlap m) (i k : ObservationLeaf W.tree)
    (σ : TerminalSpins (Configuration (n+1)) (nativeStreamingGeneratedEndpointComponent W).tree) :
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock W h (observationCommonLevel W.tree i k))
      (observationTerminalSpin W.tree i (nativeStreamingGeneratedEndpointTerminalProject W σ))
      (observationTerminalSpin W.tree k (nativeStreamingGeneratedEndpointTerminalProject W σ)) =
    cavitySpinOverlapDefect n
      (nativeStreamingGeneratedComponentClock (nativeStreamingGeneratedEndpointComponent W) h
        (observationCommonLevel (nativeStreamingGeneratedEndpointComponent W).tree
          (nativeStreamingGeneratedEndpointLeaf W i) (nativeStreamingGeneratedEndpointLeaf W k)))
      (observationTerminalSpin _ (nativeStreamingGeneratedEndpointLeaf W i) σ)
      (observationTerminalSpin _ (nativeStreamingGeneratedEndpointLeaf W k) σ) := by
  rw [nativeStreamingGeneratedEndpointOldLeaves_commonClock,
    nativeStreamingGeneratedEndpointTerminalProject_leaf,
    nativeStreamingGeneratedEndpointTerminalProject_leaf]

end QuantitativeFollowup
