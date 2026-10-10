module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageComponent
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixStreaming

@[expose] public section

/-! Whole-forest source coverage by the six computed successor families.
The original joint history and terminal test are retained. The physical
coupling multiplies the completed sum, including at zero coupling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedStreamingStep_source_coverage
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _)) M ∧
    cavityGeneratedStreamingStepSuccessorIntegralSum D μ a W M F =
      cavityGeneratedStreamingStepRawSourceIntegral D μ a W M F := by
  have hc c := cavityGeneratedStreamingComponent_source_coverage
    D μ a ha hμ W c M horder F hF C hC hbound
  have hi := integrable_finset_sum Finset.univ (fun c _=>(hc c).1)
  have he h : (∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _)) =
      ∑c : Fin W.componentCount,cavityGeneratedStreamingComponentSelectedSource D μ a W c F h := by
    apply Finset.sum_congr rfl
    intro c _
    exact cavityGeneratedStreamingComponent_source_six_eq D μ a ha hμ W c F h
  refine ⟨hi.congr (.of_forall fun h=>(he h).symm),?_⟩
  unfold cavityGeneratedStreamingStepSuccessorIntegralSum cavityGeneratedStreamingStepRawSourceIntegral
  simp_rw [(fun c=>(hc c).2)]
  rw [←integral_finset_sum _ (fun c _=>(hc c).1)]
  exact integral_congr_ae (.of_forall fun h=>(he h).symm)

theorem hasDerivWithinAt_cavityGeneratedStreamingStep_successors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M (fun h σ=>F (h,σ)))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u := by
  have H := hasDerivWithinAt_followupCavityGeneratedForestHistoryExpectation_selected_payloads
    hn β ρ hβ hρ μ a ha hfloor W M (fun h σ=>F (h,σ)) hF C hC
      (fun h σ=>hbound (h,σ)) u hu
  let D := followupCavitySpinModel n β ρ hβ hρ u hu
  have hs := cavityGeneratedStreamingStep_source_coverage
    D μ a ha hfloor W M horder F hF C hC hbound
  have he : (∫h,∑c : Fin W.componentCount,
      ∫σ,cavityGeneratedSelectedSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _) ∂M) =
      cavityGeneratedStreamingStepRawSourceIntegral D μ a W M F := by
    apply integral_congr_ae
    refine .of_forall fun h=>?_
    apply Finset.sum_congr rfl
    intro c _
    apply integral_congr_ae
    exact .of_forall fun σ=>(nativeStreamingSourceSixBracket_eq_selected_payload D μ a ha hfloor
      (W.clockTemplate.clock h c) (antitone_nat_of_succ_le (W.clockTemplate.clock_step_le h c))
      (W.clockTemplate.clock_terminal h c) (W.clockTemplate.clock_initial h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ)).symm
  rw [he,←hs.2] at H
  exact H

end QuantitativeFollowup
