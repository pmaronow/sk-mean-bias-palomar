module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTermDefinitions
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossFamiliesSupport

@[expose] public section

/-! Validity of a raw path is produced by its actual source events.
Only genuine forks are mark-labelled; unary clock levels remain free. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {C : ℕ}

theorem cavityGeneratedActualObservedRawStreamingTerm_support
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (S : CavityGeneratedObservedRawInitialForest C)
    {r m : ℕ} {W : CavityGeneratedObservedRawForest m}
    {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    (H : CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M) :
    ∀ᵐh ∂M, h ∈ W.supportSet := by
  induction H with
  | initial =>
      exact .of_forall fun h=>by
        rw [cavityGeneratedObservedRawInitialForest_supportSet]
        exact Set.mem_univ h
  | original previous c b e ih => exact ih
  | originalFresh previous c b γ ih =>
      exact cavityGeneratedObservedRawOriginalFreshChartMeasure_support μ a _ c _ γ
  | cross previous c γ δ χ ih =>
      exact cavityGeneratedObservedRawCrossChartMeasure_support μ a _ c γ δ χ _
  | current previous c γ ih =>
      exact cavityGeneratedObservedRawCurrentChartMeasure_support μ a _ c _ γ
  | future previous c γ j ih =>
      exact cavityGeneratedObservedRawFutureSourceMeasure_support μ a _ c γ j _
  | normalizer previous c ih =>
      exact cavityGeneratedObservedRawNormalizerForest_support_ae a ha.2 _ _ _ ih

end QuantitativeFollowup
