module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawTaggedComputedStepSourceCoverageTransport

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

theorem cavityGeneratedObservedRawTaggedStreamingComponent_successors_eq
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum D μ a W c M (cavityGeneratedObservedRawTaggedValue W A) =
      cavityGeneratedObservedRawTaggedStreamingComponentSuccessorIntegralSum D μ a W c M A := by
  unfold cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum
    cavityGeneratedObservedRawTaggedStreamingComponentSuccessorIntegralSum
  simp_rw [cavityGeneratedObservedRawTaggedOriginalExpectation hn D μ a W c,
    cavityGeneratedObservedRawTaggedOriginalFreshIntegral D μ a W c M _ _ A hA,
    cavityGeneratedObservedRawTaggedCrossIntegral D μ a W c M _ _ _ A hA,
    cavityGeneratedObservedRawTaggedCurrentIntegral D μ a W c M _ A hA,
    cavityGeneratedObservedRawTaggedFutureIntegral D μ a W c M _ _ A hA,
    cavityGeneratedObservedRawTaggedNormalizerExpectation D μ a W A]

theorem cavityGeneratedObservedRawTaggedStreamingStep_successors_eq
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base) :
    cavityGeneratedObservedRawStreamingStepSuccessorIntegralSum D μ a W M (cavityGeneratedObservedRawTaggedValue W A) =
      cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum D μ a W M A := by
  exact Finset.sum_congr rfl (fun c _=>
    cavityGeneratedObservedRawTaggedStreamingComponent_successors_eq hn D μ a W c M A hA)

theorem cavityGeneratedObservedRawTaggedStreamingStep_source_coverage
    (hn : 0<n) (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z,|A.base z|≤L) :
    Integrable (fun h=>∑c : Fin W.componentCount,
      ∫σ,nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree
          (fun τ=>cavityGeneratedObservedRawTaggedValue W A (h,τ)) c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock h) : Measure _)) M ∧
    cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum D μ a W M A =
      cavityGeneratedObservedRawStreamingStepRawSourceIntegral D μ a W M (cavityGeneratedObservedRawTaggedValue W A) := by
  have H := cavityGeneratedObservedRawStreamingStep_source_coverage D μ a ha hμ W M hsupport
    (cavityGeneratedObservedRawTaggedValue W A) (measurable_cavityGeneratedObservedRawTaggedValue W A hA)
    (L*2^d) (mul_nonneg hL (by positivity))
    (cavityGeneratedObservedRawTaggedValue_abs_le W A L hL hbound)
  rw [cavityGeneratedObservedRawTaggedStreamingStep_successors_eq hn D μ a W M A hA] at H
  exact H

theorem hasDerivWithinAt_cavityGeneratedObservedRawTaggedStreamingStep_successors
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hfloor : μ∈scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (A : CavityGeneratedObservedRawTaggedTest n W d) (hA : Measurable A.base)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z,|A.base z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt
      (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M
        (cavityGeneratedObservedRawTaggedValue W A))
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawTaggedStreamingStepSuccessorIntegralSum
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A)
      (Icc (0:ℝ) 1) u := by
  have H := hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_successors
    hn β ρ hβ hρ μ a ha hfloor W M hsupport (cavityGeneratedObservedRawTaggedValue W A)
    (measurable_cavityGeneratedObservedRawTaggedValue W A hA) (L*2^d)
    (mul_nonneg hL (by positivity)) (cavityGeneratedObservedRawTaggedValue_abs_le W A L hL hbound) u hu
  rw [cavityGeneratedObservedRawTaggedStreamingStep_successors_eq hn
    (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M A hA] at H
  exact H

end QuantitativeFollowup
