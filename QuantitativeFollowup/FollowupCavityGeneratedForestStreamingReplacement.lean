module
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacementBasis
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingTerminalBasisLinearity

@[expose] public section

/-! The whole-forest first bracket is the sum of actual component source
brackets with the original joint test and the untouched forest probability.
Source linearity is proved from the genuine marked laws, so the identity
also holds when the physical streaming prefactor is zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n : ℕ} {I : Type*} [Fintype I]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem component_source_basis
    {j : ℕ} (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (hq : Antitone q) (T : FiniteTerminalGenealogy j)
    (G : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingSourceSixBracket D μ a q T G =
      ∑τ : TerminalSpins (Configuration (n+1)) T,
        G τ * nativeStreamingSourceSixBracket D μ a q T (cavityGeneratedTerminalSingletonTest τ) := by
  classical
  have hδ (τ : TerminalSpins (Configuration (n+1)) T) :
      cavityGeneratedTerminalSingletonTest τ =
        (fun ξ => if ξ=τ then (1:ℝ) else 0) := by
    funext ξ
    simp only [cavityGeneratedTerminalSingletonTest]
  simp_rw [hδ]
  exact nativeStreamingSourceSixBracket_terminal_basis D μ a q hq T G

theorem cavityGeneratedNativeForest_source_partial_integral_eq_average
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap) (hq : ∀i,Antitone (q i))
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) (c : I) :
    (∫y, nativeStreamingSourceSixBracket D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c y)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
      nativeStreamingSourceSixBracket D μ a (q c) (T c)
        (cavityGeneratedForestAveragedPartialTerminalTest D μ a J T q F c) :=
  cavityGeneratedNativeForest_partial_functional_integral D μ a J T q F c
    (nativeStreamingSourceSixBracket D μ a (q c) (T c))
    (component_source_basis D μ a (q c) (hq c) (T c))

theorem cavityGeneratedNativeForest_first_bracket_replacement
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap) (hq : ∀i,Antitone (q i))
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ) :
    (∑σ : CavityGeneratedForestTerminalSample (n := n) J T,
      F σ * ∑c : I,nativeStreamingSourceSixBracket D μ a (q c) (T c)
        (cavityGeneratedTerminalSingletonTest (σ c)) *
          ∏d∈Finset.univ.erase c,nativeStreamingOldTerminalExpectation D μ a (q d) (T d)
            (cavityGeneratedTerminalSingletonTest (σ d))) =
      ∑c : I, ∫y,nativeStreamingSourceSixBracket D μ a (q c) (T c)
        (cavityGeneratedForestPartialTerminalTest J T F c y)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _) := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  have he := cavityGeneratedNativeForest_partial_functional_basis D μ a J T q F c
    (nativeStreamingSourceSixBracket D μ a (q c) (T c))
    (component_source_basis D μ a (q c) (hq c) (T c))
  rw [he]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem cavityGeneratedForestFirstStreamingBracket_eq_component_integrals
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : I → ℕ)
    (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap) (hq : ∀i,Antitone (q i))
    (F : CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    cavityGeneratedForestFirstStreamingBracket β ρ hβ hρ μ a J T q F u hu =
      ∑c : I, ∫y,nativeStreamingSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
        μ a (q c) (T c) (cavityGeneratedForestPartialTerminalTest J T F c y)
        ∂(cavityGeneratedNativeForestTerminalProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a J T q : Measure _) := by
  classical
  unfold cavityGeneratedForestFirstStreamingBracket
  have hp (σ : CavityGeneratedForestTerminalSample (n := n) J T) (d : I) :
      followupCavityNativeTerminalExpectation n β ρ hβ hρ μ a (q d) (T d)
        (cavityGeneratedTerminalSingletonTest (σ d)) u =
        nativeStreamingOldTerminalExpectation (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d)) :=
    followupCavityNativeTerminalExpectation_eq_old_terminal β ρ hβ hρ μ a
      (q d) (T d) (cavityGeneratedTerminalSingletonTest (σ d)) u hu
  simp_rw [hp]
  exact cavityGeneratedNativeForest_first_bracket_replacement _ μ a J T q hq F

end QuantitativeFollowup
