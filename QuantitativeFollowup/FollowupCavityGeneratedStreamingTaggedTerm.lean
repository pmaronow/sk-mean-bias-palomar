module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTermDefinitions
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedTestBounds

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

theorem cavityGeneratedActualTaggedStreamingTerm_path
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) :
    CavityGeneratedActualStreamingTerm μ a S r m W M := by
  induction H with
  | initial => exact .initial
  | original previous c i k ih => exact .original ih c i k
  | originalFresh previous c i γ ih => exact .originalFresh ih c i γ
  | cross previous c γ δ χ ih => exact .cross ih c γ δ χ
  | current previous c γ ih => exact .current ih c γ
  | future previous c γ j ih => exact .future ih c γ j
  | normalizer previous c ih => exact .normalizer ih c

private theorem taggedPrefix_measurable (m : ℕ) :
    Measurable (cavityGeneratedHistoryPrefix : CavityGeneratedHistory Paper.Overlap (m+1) →
      CavityGeneratedHistory Paper.Overlap m) := by
  exact measurable_pi_iff.mpr fun i=>measurable_pi_apply i.castSucc

theorem cavityGeneratedActualTaggedStreamingTerm_base_measurable
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ) (hF : Measurable F)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) : Measurable A.base := by
  induction H with
  | initial => exact hF
  | original previous c i k ih => exact ih
  | @originalFresh r m W M A previous c i γ ih =>
      exact ih.comp (((taggedPrefix_measurable m).comp measurable_fst).prodMk
        ((measurable_of_finite (cavityGeneratedSingleOriginOldTerminal W c γ .single)).comp measurable_snd))
  | @cross r m W M A previous c γ δ χ ih =>
      exact ih.comp ((((taggedPrefix_measurable m).comp (taggedPrefix_measurable (m+1))).comp
        measurable_fst).prodMk
        ((measurable_of_finite (cavityGeneratedCrossOriginOldTerminal W c γ δ χ)).comp measurable_snd))
  | @current r m W M A previous c γ ih =>
      exact ih.comp (((taggedPrefix_measurable m).comp measurable_fst).prodMk
        ((measurable_of_finite (cavityGeneratedSingleOriginOldTerminal W c γ .current)).comp measurable_snd))
  | @future r m W M A previous c γ j ih =>
      exact ih.comp ((((taggedPrefix_measurable m).comp (taggedPrefix_measurable (m+1))).comp
        measurable_fst).prodMk
        ((measurable_of_finite (cavityGeneratedFutureOriginOldTerminal W c γ j)).comp measurable_snd))
  | @normalizer r m W M A previous c ih =>
      exact ih.comp (((taggedPrefix_measurable m).comp measurable_fst).prodMk
        ((measurable_of_finite (printedGeneratedNormalizerOldTerminalProjection W)).comp measurable_snd))

theorem cavityGeneratedActualTaggedStreamingTerm_base_abs_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (L : ℝ) (hF : ∀z,|F z|≤L)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) : ∀z,|A.base z|≤L := by
  induction H with
  | initial => exact hF
  | original previous c i k ih => exact ih
  | originalFresh previous c i γ ih => exact fun z=>ih _
  | cross previous c γ δ χ ih => exact fun z=>ih _
  | current previous c γ ih => exact fun z=>ih _
  | future previous c γ j ih => exact fun z=>ih _
  | normalizer previous c ih => exact fun z=>ih _

theorem cavityGeneratedActualTaggedStreamingTerm_value_measurable
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ) (hF : Measurable F)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) :
    Measurable (cavityGeneratedTaggedTestValue W A) :=
  measurable_cavityGeneratedTaggedTestValue W A
    (cavityGeneratedActualTaggedStreamingTerm_base_measurable μ a S F hF H)

theorem cavityGeneratedActualTaggedStreamingTerm_value_abs_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (S : Fin C → CavityGeneratedSiblingShape)
    (F : CavityGeneratedHistory Paper.Overlap 1 ×
      CavityGeneratedForestTerminalSample (n:=n) (cavityGeneratedInitialSiblingForest S).depth
        (cavityGeneratedInitialSiblingForest S).tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hF : ∀z,|F z|≤L)
    {W : CavityGeneratedConstructedForest m} {M : Measure (CavityGeneratedHistory Paper.Overlap m)}
    {A : CavityGeneratedTaggedTest n W r}
    (H : CavityGeneratedActualTaggedStreamingTerm μ a S F r m W M A) :
    ∀z,|cavityGeneratedTaggedTestValue W A z|≤L*2^r :=
  cavityGeneratedTaggedTestValue_abs_le W A L hL
    (cavityGeneratedActualTaggedStreamingTerm_base_abs_le μ a S F L hF H)

end QuantitativeFollowup
