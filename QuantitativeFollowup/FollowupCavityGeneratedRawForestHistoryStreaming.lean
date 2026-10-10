module
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingBase
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacement

@[expose] public section

/-! Actual component replacement inside the genuine whole-history
streaming identity. The original history and full joint terminal test
are retained in the independent forest probability at every point. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n C : ℕ} {X : Type*} [MeasurableSpace X]
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followupCavityGeneratedRawForestHistoryFirstResponse_eq_component_integrals
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (hq : ∀h c, Antitone (q h c))
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (h : X) :
    followupCavityGeneratedRawForestHistoryFirstResponse β ρ hβ hρ μ a J T q F u h =
      (followupCavityAlpha n β ρ/2)*∑c : Fin C,
        ∫y,nativeStreamingSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a (q h c) (T c)
          (cavityGeneratedForestPartialTerminalTest J T (F h) c y)
          ∂(cavityGeneratedNativeForestTerminalProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
            μ a J T (q h) : Measure _) := by
  simp only [followupCavityGeneratedRawForestHistoryFirstResponse,dif_pos hu]
  rw [cavityGeneratedForestFirstStreamingBracket_eq_component_integrals
    β ρ hβ hρ μ a J T (q h)
    (hq h) (F h) u hu]

theorem hasDerivWithinAt_followupCavityGeneratedRawForestHistoryExpectation_replacement
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (J : Fin C → ℕ) (T : (c : Fin C) → FiniteTerminalGenealogy (J c))
    (q : X → Fin C → ℕ → Paper.Overlap)
    (M : Measure X) [IsFiniteMeasure M]
    (F : X →
      CavityGeneratedForestTerminalSample (n := n) J T → ℝ)
    (hqm : ∀c j, Measurable (fun h => q h c j))
    (hq : ∀h c, Antitone (q h c)) (hJ : ∀c, 0<J c)
    (hzero : ∀h c, (q h c 0 : ℝ)=1)
    (htop : ∀h c, (q h c (J c) : ℝ)=0)
    (hF : Measurable (Function.uncurry F)) (L : ℝ) (hL : 0≤L)
    (hbound : ∀h σ,|F h σ|≤L) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedRawForestHistoryExpectation β ρ hβ hρ μ a J T q M F)
      ((followupCavityAlpha n β ρ/2)*∫h,∑c : Fin C,
        ∫y,nativeStreamingSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a (q h c) (T c)
          (cavityGeneratedForestPartialTerminalTest J T (F h) c y)
          ∂(cavityGeneratedNativeForestTerminalProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
            μ a J T (q h) : Measure _) ∂M)
      (Icc (0:ℝ) 1) u := by
  have H := (followupCavityGeneratedRawForestHistory_streaming_data
    hn β ρ hβ hρ μ a ha hfloor J T q M F hqm hq hJ hzero htop hF L hL hbound u hu).2
  have he := integral_congr_ae (μ := M) (.of_forall fun h =>
    followupCavityGeneratedRawForestHistoryFirstResponse_eq_component_integrals
      β ρ hβ hρ μ a J T q F hq u hu h)
  rw [integral_const_mul] at he
  rw [he] at H
  exact H

end QuantitativeFollowup
