module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageComponent

@[expose] public section

/-! An actual raw whole-forest streaming step is the finite sum of its
six computed successor families. The physical coupling is exterior;
all old terminal coordinates and the original retained history survive. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

theorem cavityGeneratedObservedRawStreamingStep_source_coverage
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M, h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L) :
    Integrable (fun h => ∑c : Fin W.componentCount,
      ∫σ, nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock h) : Measure _)) M ∧
    cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum D μ a W M F =
      cavityGeneratedObservedRawStreamingStepRawSourceIntegral D μ a W M F := by
  have hc c := cavityGeneratedObservedRawStreamingComponent_source_coverage
    D μ a ha hμ W c M hsupport F hF L hL hbound
  have hi := integrable_finset_sum Finset.univ (fun c _ => (hc c).1)
  have he h : (∑c : Fin W.componentCount,
      ∫σ, nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock h) : Measure _)) =
      ∑c : Fin W.componentCount, cavityGeneratedObservedRawStreamingComponentSelectedSource D μ a W c F h := by
    apply Finset.sum_congr rfl
    intro c _
    exact cavityGeneratedObservedRawStreamingComponent_source_six_eq D μ a ha hμ W c F h
  refine ⟨hi.congr (.of_forall fun h => (he h).symm), ?_⟩
  unfold cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum
    cavityGeneratedObservedRawStreamingStepRawSourceIntegral
  simp_rw [(fun c => (hc c).2)]
  rw [←integral_finset_sum _ (fun c _ => (hc c).1)]
  exact integral_congr_ae (.of_forall fun h => (he h).symm)

theorem hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_successors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M, h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u := by
  have hd := hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_raw_source
    hn β ρ hβ hρ μ a ha hμ W M F hF L hL hbound u hu
  have hs := cavityGeneratedObservedRawStreamingStep_source_coverage
    (followupCavitySpinModel n β ρ hβ hρ u hu) μ a ha hμ W M hsupport F hF L hL hbound
  rw [←hs.2] at hd
  exact hd

end QuantitativeFollowup
