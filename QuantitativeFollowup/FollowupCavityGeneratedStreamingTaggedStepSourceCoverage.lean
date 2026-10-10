module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingTaggedStepSourceCoverageTransport

@[expose] public section

/-! A genuine source step on a tagged whole-forest test equals the sum
of its six computed tagged successors. The only test assumptions concern
the initial joint base observable; all physical tag bounds are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m d : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedTaggedStreamingComponent_successors_eq
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    cavityGeneratedStreamingComponentSuccessorIntegralSum D μ a W c M (cavityGeneratedTaggedTestValue W A) =
      cavityGeneratedTaggedStreamingComponentSuccessorIntegralSum D μ a W c M A := by
  unfold cavityGeneratedStreamingComponentSuccessorIntegralSum
    cavityGeneratedTaggedStreamingComponentSuccessorIntegralSum
  simp_rw [cavityGeneratedTaggedOriginalExpectation hn D μ a W c,
    cavityGeneratedTaggedOriginalFreshIntegral D μ a W c M _ _ A hA,
    cavityGeneratedTaggedCrossIntegral D μ a W c M _ _ _ A hA,
    cavityGeneratedTaggedCurrentIntegral D μ a W c M _ A hA,
    cavityGeneratedTaggedFutureIntegral D μ a W c M _ _ A hA,
    cavityGeneratedTaggedNormalizerExpectation D μ a W A]

theorem cavityGeneratedTaggedStreamingStep_successors_eq
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base) :
    cavityGeneratedStreamingStepSuccessorIntegralSum D μ a W M (cavityGeneratedTaggedTestValue W A) =
      cavityGeneratedTaggedStreamingStepSuccessorIntegralSum D μ a W M A := by
  exact Finset.sum_congr rfl (fun c _=>
    cavityGeneratedTaggedStreamingComponent_successors_eq hn D μ a W c M A hA)

theorem cavityGeneratedTaggedStreamingStep_source_coverage
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z,|A.base z|≤L) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree
          (fun τ=>cavityGeneratedTaggedTestValue W A (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _)) M ∧
    cavityGeneratedTaggedStreamingStepSuccessorIntegralSum D μ a W M A =
      cavityGeneratedStreamingStepRawSourceIntegral D μ a W M (cavityGeneratedTaggedTestValue W A) := by
  have H := cavityGeneratedStreamingStep_source_coverage D μ a ha hμ W M horder
    (cavityGeneratedTaggedTestValue W A) (measurable_cavityGeneratedTaggedTestValue W A hA)
    (L*2^d) (mul_nonneg hL (by positivity))
    (cavityGeneratedTaggedTestValue_abs_le W A L hL hbound)
  rw [cavityGeneratedTaggedStreamingStep_successors_eq hn D μ a W M A hA] at H
  exact H

theorem hasDerivWithinAt_cavityGeneratedTaggedStreamingStep_successors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (A : CavityGeneratedTaggedTest n W d) (hA : Measurable A.base)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z,|A.base z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedForestHistoryExpectation β ρ hβ hρ μ a W M
        (fun h σ=>cavityGeneratedTaggedTestValue W A (h,σ)))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u := by
  have H := hasDerivWithinAt_cavityGeneratedStreamingStep_successors
    hn β ρ hβ hρ μ a ha hfloor W M horder (cavityGeneratedTaggedTestValue W A)
    (measurable_cavityGeneratedTaggedTestValue W A hA) (L*2^d)
    (mul_nonneg hL (by positivity)) (cavityGeneratedTaggedTestValue_abs_le W A L hL hbound) u hu
  rw [cavityGeneratedTaggedStreamingStep_successors_eq hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A hA] at H
  exact H

end QuantitativeFollowup
