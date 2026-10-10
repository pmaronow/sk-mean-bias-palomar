module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTermDefinitions

@[expose] public section

/-! The computed mark measure of every real source path is supported on
its computed forest order. This is derived from the receiver constructors,
including root padding and repeated cells; it is not a supplied path input. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {C : ℕ}

theorem cavityGeneratedActualStreamingTerm_order
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (S : Fin C → CavityGeneratedSiblingShape)
    {r m : ℕ} {W : CavityGeneratedConstructedForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualStreamingTerm μ a S r m W M) :
    ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet := by
  induction H with
  | initial => exact printedGeneratedInitialSiblingForest_order_ae S _
  | original previous c b e ih => exact ih
  | originalFresh previous c b γ ih =>
      exact cavityGeneratedOriginalFreshChartMeasure_order μ a _ c _ γ
  | cross previous c γ δ χ ih =>
      exact cavityGeneratedCrossOriginChartMeasure_order μ a _ c _ γ δ χ
  | current previous c γ ih =>
      exact cavityGeneratedCurrentChartMeasure_order μ a _ c _ γ
  | future previous c γ j ih =>
      exact cavityGeneratedFutureOriginChartSourceMeasure_order μ a _ c _ γ j
  | normalizer previous c ih =>
      exact cavityGeneratedNormalizerFamily_order_ae a ha.2 _ _ _ ih

end QuantitativeFollowup
