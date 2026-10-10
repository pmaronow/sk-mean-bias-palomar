module
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingRefinementTerminalMoments
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingSourceBracket

@[expose] public section

/-! Observation refinement preserves the actual original pair sum and the
independent normalizer term. Unary padding adds no terminal leaves. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n J : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem nativeStreamingPadLeafEmbed_surjective {j : ℕ}
    (T : FiniteTerminalGenealogy j) (k : ℕ) :
    Function.Surjective (observationPadLeafEmbed T k) := by
  induction k with
  | zero => exact Function.surjective_id
  | succ k ih => exact ih

theorem nativeStreamingRefinementLeafEmbed_surjective (d : ℕ → ℕ)
    (T : FiniteTerminalGenealogy J) :
    Function.Surjective (observationRefinementLeafEmbed d T) := by
  induction T with
  | leaf => exact Function.surjective_id
  | @advance j T ih =>
      exact (nativeStreamingPadLeafEmbed_surjective (observationRefineTree d T) (d j)).comp ih
  | fork T U ihT ihU =>
      intro x
      cases x with
      | inl x =>
          obtain ⟨i, hi⟩ := ihT x
          exact ⟨Sum.inl i, congrArg Sum.inl hi⟩
      | inr x =>
          obtain ⟨i, hi⟩ := ihU x
          exact ⟨Sum.inr i, congrArg Sum.inr hi⟩

def nativeStreamingRefinementLeafEquiv (d : ℕ → ℕ)
    (T : FiniteTerminalGenealogy J) : ObservationLeaf T ≃ ObservationLeaf (observationRefineTree d T) :=
  Equiv.ofBijective (observationRefinementLeafEmbed d T)
    ⟨observationRefinementLeafEmbed_injective d T,
      nativeStreamingRefinementLeafEmbed_surjective d T⟩

theorem nativeStreamingPatternMoment_original_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j) = q j)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ)
    (i k : ObservationLeaf T) :
    nativeStreamingPatternMoment D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F)
      (.original (observationRefinementLeafEmbed d T i) (observationRefinementLeafEmbed d T k)) =
      nativeStreamingPatternMoment D μ a q T F (.original i k) := by
  classical
  by_cases hik : i=k
  · subst k
    simp only [nativeStreamingPatternMoment, ite_true]
  · have hfik : observationRefinementLeafEmbed d T i ≠ observationRefinementLeafEmbed d T k :=
      fun h => hik (observationRefinementLeafEmbed_injective d T h)
    simp only [nativeStreamingPatternMoment, if_neg hik, if_neg hfik,
      observationRefinementLeafEmbed_commonLevel, hlevels]
    let G := fun σ : TerminalSpins (Configuration (n+1)) T =>
      F σ*cavitySpinOverlapDefect n (q (observationCommonLevel T i k))
        (observationTerminalSpin T i σ) (observationTerminalSpin T k σ)
    have H := nativeStreamingOldTerminalIntegral_refinement D μ a q Q d hQ hlevels T G
    simpa only [G, nativeStreamingRefinedTerminalTest, Function.comp_apply,
      observationTerminalSpin_record, nativeStreamingRefinementTerminalProject_record,
      observationRefinementLeafEmbed_spin] using H

theorem nativeStreamingSourceOriginalTerm_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j) = q j)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceOriginalTerm D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F) =
      nativeStreamingSourceOriginalTerm D μ a q T F := by
  classical
  unfold nativeStreamingSourceOriginalTerm
  let E := nativeStreamingRefinementLeafEquiv d T
  symm
  apply Fintype.sum_equiv E
  intro i
  apply Fintype.sum_equiv E
  intro k
  exact (nativeStreamingPatternMoment_original_refinement D μ a q Q d hQ hlevels T F i k).symm

theorem nativeStreamingOldTerminalExpectation_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j) = q j)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingOldTerminalExpectation D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F) = nativeStreamingOldTerminalExpectation D μ a q T F :=
  nativeStreamingOldTerminalIntegral_refinement D μ a q Q d hQ hlevels T F

theorem nativeStreamingSourceNormalizerTerm_refinement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q Q : ℕ → Paper.Overlap) (d : ℕ → ℕ) (hQ : Antitone Q)
    (hlevels : ∀j, Q (observationRefinementDepth d j) = q j)
    (T : FiniteTerminalGenealogy J) (F : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceNormalizerTerm D μ a Q (observationRefineTree d T)
      (nativeStreamingRefinedTerminalTest d T F) = nativeStreamingSourceNormalizerTerm D μ a q T F := by
  rw [nativeStreamingSourceNormalizerTerm_eq_independent,
    nativeStreamingSourceNormalizerTerm_eq_independent,
    nativeStreamingOldTerminalExpectation_refinement D μ a q Q d hQ hlevels T F]

end QuantitativeFollowup
