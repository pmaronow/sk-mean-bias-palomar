module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingMarkCoherence
public import FourPapersCommon.FiniteCascadeContinuationVertexGeometry

@[expose] public section

/-! A mark's common-history clock with a fixed old vertex is unchanged
at every fork root. This is structural coherence of the actual retained
state and ancestry, including repeated physical clocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S A : Type} [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
set_option maxHeartbeats 900000

theorem nativeStreamingVertexStateCommonPath_root_coherent
    (H : ℕ → ℕ → E → ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (w : FiniteCascadeRecordVertex T) (x : E) (z : Records E S T) :
    nativeStreamingRootCoherent T (fun v =>
      H v.depth (finiteCascadeCommonPathDepth T v w)
        (nativeStreamingVertexState v x z)) := by
  induction T generalizing x with
  | leaf => trivial
  | @advance j T ih =>
      cases w with
      | root =>
          simpa only [finiteCascadeCommonPathDepth_root_right] using
            nativeStreamingVertexState_root_coherent (fun k y => H k (j+1) y) (.advance T) x z
      | child w => exact ih w z.1 z.2
  | @fork j T U ihT ihU =>
      cases w with
      | root =>
          simpa only [finiteCascadeCommonPathDepth_root_right] using
            nativeStreamingVertexState_root_coherent (fun k y => H k j y) (.fork T U) x z
      | left w =>
          refine ⟨?_, rfl, ihT w x z.1, ?_⟩
          · change H j (finiteCascadeCommonPathDepth T (.root T) w) x = H j j x
            rw [finiteCascadeCommonPathDepth_root_left]
          · exact nativeStreamingVertexState_root_coherent (fun k y => H k j y) U x z.2
      | right w =>
          refine ⟨rfl, ?_, ?_, ihU w x z.2⟩
          · change H j (finiteCascadeCommonPathDepth U (.root U) w) x = H j j x
            rw [finiteCascadeCommonPathDepth_root_left]
          · exact nativeStreamingVertexState_root_coherent (fun k y => H k j y) T x z.1

theorem nativeStreamingRootCoherent_const {j : ℕ}
    (T : FiniteTerminalGenealogy j) (c : ℝ) :
    nativeStreamingRootCoherent T (fun _ => c) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih
  | fork T U ihT ihU => exact ⟨rfl, rfl, ihT, ihU⟩

theorem nativeStreamingCommonPath_root_coherent (H : ℕ → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T) :
    nativeStreamingRootCoherent T
      (fun v => H (finiteCascadeCommonPathDepth T v w)) := by
  induction T with
  | leaf => trivial
  | @advance j T ih =>
      cases w with
      | root =>
          simpa only [finiteCascadeCommonPathDepth_root_right] using
            nativeStreamingRootCoherent_const (.advance T) (H (j+1))
      | child w => exact ih w
  | @fork j T U ihT ihU =>
      cases w with
      | root =>
          simpa only [finiteCascadeCommonPathDepth_root_right] using
            nativeStreamingRootCoherent_const (.fork T U) (H j)
      | left w =>
          refine ⟨?_, rfl, ihT w, nativeStreamingRootCoherent_const U (H j)⟩
          change H (finiteCascadeCommonPathDepth T (.root T) w) = H j
          rw [finiteCascadeCommonPathDepth_root_left]
      | right w =>
          refine ⟨rfl, ?_, nativeStreamingRootCoherent_const T (H j), ihU w⟩
          change H (finiteCascadeCommonPathDepth U (.root U) w) = H j
          rw [finiteCascadeCommonPathDepth_root_left]

theorem nativeStreamingVertexStateCommonPath_integral_root_coherent
    {j : ℕ} (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T)
    (P : Measure (E × Records E S T))
    (H : (E × Records E S T) → ℕ → ℕ → E → ℝ) :
    nativeStreamingRootCoherent T (fun v => ∫z,
      H z v.depth (finiteCascadeCommonPathDepth T v w)
        (nativeStreamingVertexState v z.1 z.2) ∂P) :=
  nativeStreamingRootCoherent_integral P T _
    (fun z => nativeStreamingVertexStateCommonPath_root_coherent (H z) T w z.1 z.2)

theorem nativeStreamingConditionalMarkCommonPath_integral_root_coherent
    {j : ℕ} (T : FiniteTerminalGenealogy j) (w : FiniteCascadeRecordVertex T)
    (P : Measure (E × Records E S T)) (K : ℕ → E → Measure A)
    (F : (E × Records E S T) → ℕ → A → ℝ) :
    nativeStreamingRootCoherent T (fun v => ∫z, ∫a,
      F z (finiteCascadeCommonPathDepth T v w) a
        ∂K v.depth (nativeStreamingVertexState v z.1 z.2) ∂P) :=
  nativeStreamingVertexStateCommonPath_integral_root_coherent T w P
    (fun z k c x => ∫a, F z c a ∂K k x)

end QuantitativeFollowup
