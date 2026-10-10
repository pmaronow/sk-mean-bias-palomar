module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingObservationGraft
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingCharges

@[expose] public section

/-! At a fork, the two child roots retain the same physical state and
clock. Actual conditional mark integrals therefore satisfy the coherence
needed for charge regrouping, before and after averaging the complete
old record. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon FiniteTerminalGenealogy
variable {E S A : Type} [MeasurableSpace E] [MeasurableSpace S] [MeasurableSpace A]
set_option maxHeartbeats 900000

theorem nativeStreamingVertexState_root_coherent (H : ℕ → E → ℝ)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (x : E) (z : Records E S T) :
    nativeStreamingRootCoherent T
      (fun v => H v.depth (nativeStreamingVertexState v x z)) := by
  induction T generalizing x with
  | leaf => trivial
  | advance T ih => exact ih z.1 z.2
  | fork T U ihT ihU =>
      exact ⟨rfl, rfl, ihT x z.1, ihU x z.2⟩

theorem nativeStreamingRootCoherent_integral (P : Measure A)
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (Φ : A → FiniteCascadeRecordVertex T → ℝ)
    (hΦ : ∀z, nativeStreamingRootCoherent T (Φ z)) :
    nativeStreamingRootCoherent T (fun v => ∫z, Φ z v ∂P) := by
  induction T with
  | leaf => trivial
  | advance T ih => exact ih (fun z v => Φ z (.child v)) hΦ
  | fork T U ihT ihU =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact integral_congr_ae (.of_forall fun z => (hΦ z).1)
      · exact integral_congr_ae (.of_forall fun z => (hΦ z).2.1)
      · exact ihT (fun z v => Φ z (.left v)) (fun z => (hΦ z).2.2.1)
      · exact ihU (fun z v => Φ z (.right v)) (fun z => (hΦ z).2.2.2)

theorem nativeStreamingVertexState_integral_root_coherent
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (P : Measure (E × Records E S T))
    (H : (E × Records E S T) → ℕ → E → ℝ) :
    nativeStreamingRootCoherent T
      (fun v => ∫z, H z v.depth (nativeStreamingVertexState v z.1 z.2) ∂P) :=
  nativeStreamingRootCoherent_integral P T _
    (fun z => nativeStreamingVertexState_root_coherent (H z) T z.1 z.2)

theorem nativeStreamingConditionalMark_integral_root_coherent
    {j : ℕ} (T : FiniteTerminalGenealogy j)
    (P : Measure (E × Records E S T)) (K : ℕ → E → Measure A)
    (F : (E × Records E S T) → A → ℝ) :
    nativeStreamingRootCoherent T
      (fun v => ∫z, ∫a, F z a ∂K v.depth (nativeStreamingVertexState v z.1 z.2) ∂P) :=
  nativeStreamingVertexState_integral_root_coherent T P (fun z k x => ∫a, F z a ∂K k x)

end QuantitativeFollowup
