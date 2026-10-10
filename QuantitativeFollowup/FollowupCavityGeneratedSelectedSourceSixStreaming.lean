module
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSix
public import QuantitativeFollowup.FollowupCavityGeneratedForestHistoryStreaming

@[expose] public section

/-! The genuine retained-history streaming producer with all six
selected payload integrals. The original joint test is replaced in one
component, and every other component keeps its actual probability law.
The physical prefactor remains outside the source and history integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem followupCavityGeneratedForestHistoryFirstResponse_eq_selected_payloads
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) (h : CavityGeneratedHistory Paper.Overlap m) :
    followupCavityGeneratedForestHistoryFirstResponse β ρ hβ hρ μ a W F u h=
      (followupCavityAlpha n β ρ/2)*∑c : Fin W.componentCount,
        ∫y,cavityGeneratedSelectedSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a (W.clockTemplate.clock h c) (W.tree c)
          (cavityGeneratedForestPartialTerminalTest W.depth W.tree (F h) c y)
          ∂(cavityGeneratedNativeForestTerminalProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
            μ a W.depth W.tree (W.clockTemplate.clock h) : Measure _) := by
  rw [followupCavityGeneratedForestHistoryFirstResponse_eq_component_integrals
    β ρ hβ hρ μ a W F u hu h]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  apply integral_congr_ae
  exact .of_forall fun y => nativeStreamingSourceSixBracket_eq_selected_payload _ μ a ha hfloor
    (W.clockTemplate.clock h c)
    (antitone_nat_of_succ_le (W.clockTemplate.clock_step_le h c))
    (W.clockTemplate.clock_terminal h c) (W.clockTemplate.clock_initial h c)
    (W.tree c) (cavityGeneratedForestPartialTerminalTest W.depth W.tree (F h) c y)

theorem hasDerivWithinAt_followupCavityGeneratedForestHistoryExpectation_selected_payloads
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m →
      CavityGeneratedForestTerminalSample (n := n) W.depth W.tree → ℝ)
    (hF : Measurable (Function.uncurry F)) (C : ℝ) (hC : 0≤C)
    (hbound : ∀h σ,|F h σ|≤C) (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*∫h,∑c : Fin W.componentCount,
        ∫y,cavityGeneratedSelectedSourceSixBracket (followupCavitySpinModel n β ρ hβ hρ u hu)
          μ a (W.clockTemplate.clock h c) (W.tree c)
          (cavityGeneratedForestPartialTerminalTest W.depth W.tree (F h) c y)
          ∂(cavityGeneratedNativeForestTerminalProbability (followupCavitySpinModel n β ρ hβ hρ u hu)
            μ a W.depth W.tree (W.clockTemplate.clock h) : Measure _) ∂M)
      (Icc (0:ℝ) 1) u := by
  have H := hasDerivWithinAt_followupCavityGeneratedForestHistoryExpectation
    hn β ρ hβ hρ μ a ha hfloor W M F hF C hC hbound u hu
  have he := integral_congr_ae (μ := M) (.of_forall fun h =>
    followupCavityGeneratedForestHistoryFirstResponse_eq_selected_payloads
      β ρ hβ hρ μ a ha hfloor W F u hu h)
  rw [integral_const_mul] at he
  rw [he] at H
  exact H

end QuantitativeFollowup
