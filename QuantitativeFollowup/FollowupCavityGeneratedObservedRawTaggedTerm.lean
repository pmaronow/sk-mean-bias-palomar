module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTaggedTermDefinitions
public import QuantitativeFollowup.SupportingGeneratedObservedRawTaggedBounds

@[expose] public section

/-! A recursively transformed tagged source test has its real path,
measurability, and count-only observable bound derived from its initial test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n C r m : ℕ}

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_path
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) :
    CavityGeneratedActualObservedRawStreamingTerm μ a S r m W M := by
  induction H with
  | initial => exact .initial
  | original previous c i k ih => exact .original ih c i k
  | originalFresh previous c i γ ih => exact .originalFresh ih c i γ
  | cross previous c γ δ χ ih => exact .cross ih c γ δ χ
  | current previous c γ ih => exact .current ih c γ
  | future previous c γ j ih => exact .future ih c γ j
  | normalizer previous c ih => exact .normalizer ih c

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_base_measurable
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ) (hF : Measurable F)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) : Measurable A.base := by
  induction H with
  | initial => exact hF
  | original previous c i k ih => exact ih
  | @originalFresh r m W M A previous c i γ ih =>
      exact cavityGeneratedObservedRawSingleOriginOriginalFreshTaggedTest_base_measurable W c γ i A ih
  | @cross r m W M A previous c γ δ χ ih =>
      exact measurable_cavityGeneratedObservedRawCrossTaggedTest_base W c γ δ χ A ih
  | @current r m W M A previous c γ ih =>
      exact cavityGeneratedObservedRawSingleOriginCurrentTaggedTest_base_measurable W c γ A ih
  | @future r m W M A previous c γ j ih =>
      exact measurable_cavityGeneratedObservedRawFutureTaggedTest_base W c γ j A ih
  | @normalizer r m W M A previous c ih =>
      exact measurable_cavityGeneratedObservedRawNormalizerTaggedSuccessor_base W A ih

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_base_abs_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    (L : ℝ) (hF : ∀z,|F z|≤L)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) : ∀z,|A.base z|≤L := by
  induction H with
  | initial => exact hF
  | original previous c i k ih => exact ih
  | originalFresh previous c i γ ih => exact fun z=>ih _
  | cross previous c γ δ χ ih => exact fun z=>ih _
  | current previous c γ ih => exact fun z=>ih _
  | future previous c γ j ih => exact fun z=>ih _
  | normalizer previous c ih => exact fun z=>ih _

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_value_measurable
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ) (hF : Measurable F)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) :
    Measurable (cavityGeneratedObservedRawTaggedValue W A) :=
  measurable_cavityGeneratedObservedRawTaggedValue W A
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_measurable μ a S F hF H)

theorem cavityGeneratedActualObservedRawTaggedStreamingTerm_value_abs_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : CavityGeneratedObservedRawInitialForest C)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedObservedRawInitialForest S).depth
        (cavityGeneratedObservedRawInitialForest S).tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hF : ∀z,|F z|≤L)
    {W : CavityGeneratedObservedRawForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedObservedRawTaggedTest n W r}
    (H : CavityGeneratedActualObservedRawTaggedStreamingTerm μ a S F r m W M A) :
    ∀z,|cavityGeneratedObservedRawTaggedValue W A z|≤L*2^r :=
  cavityGeneratedObservedRawTaggedValue_abs_le W A L hL
    (cavityGeneratedActualObservedRawTaggedStreamingTerm_base_abs_le μ a S F L hF H)

end QuantitativeFollowup
