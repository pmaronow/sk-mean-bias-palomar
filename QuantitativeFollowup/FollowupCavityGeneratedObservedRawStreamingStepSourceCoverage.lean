module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverageStatic
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreaming

@[expose] public section

/-! Actual history streaming of a raw observed forest. Arbitrary unary
clock slices remain in the true terminal probability. The source is the
six original selected-payload integrals, before graft-chart replacement;
the physical coupling is exterior and every partial test retains the
whole original joint observable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def followupCavityGeneratedObservedRawForestHistoryExpectation
    (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (u : ℝ) : ℝ :=
  followupCavityGeneratedRawForestHistoryExpectation β ρ hβ hρ μ a
    W.depth W.tree W.clock M (fun h σ => F (h,σ)) u

def cavityGeneratedObservedRawStreamingStepRawSourceIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  ∫h,∑c : Fin W.componentCount,
    ∫σ,nativeStreamingSourceSixBracket D μ a (W.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h,τ)) c σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _) ∂M

def cavityGeneratedObservedRawStreamingStepSelectedSourceIntegral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) : ℝ :=
  ∫h,∑c : Fin W.componentCount,
    cavityGeneratedObservedRawStreamingComponentSelectedSource D μ a W c F h ∂M

theorem cavityGeneratedObservedRawStreamingStep_source_six_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) :
    cavityGeneratedObservedRawStreamingStepRawSourceIntegral D μ a W M F =
      cavityGeneratedObservedRawStreamingStepSelectedSourceIntegral D μ a W M F := by
  apply integral_congr_ae
  exact .of_forall fun h => Finset.sum_congr rfl fun c _ =>
    cavityGeneratedObservedRawStreamingComponent_source_six_eq D μ a ha hμ W c F h

private theorem observedRaw_depth_pos (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) : 0<W.depth c := by
  by_contra h
  have hd : W.depth c=0 := by omega
  have hi := W.clock_initial (fun _ => 0) c
  rw [hd,W.clock_terminal] at hi
  have hh := congrArg (fun x : Paper.Overlap => (x:ℝ)) hi
  norm_num at hh

theorem hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_raw_source
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawStreamingStepRawSourceIntegral
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u := by
  exact hasDerivWithinAt_followupCavityGeneratedRawForestHistoryExpectation_replacement
    hn β ρ hβ hρ μ a ha hμ W.depth W.tree W.clock M (fun h σ => F (h,σ))
    W.measurable_clock W.clock_antitone (observedRaw_depth_pos W)
    (fun h c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clock_terminal h c))
    (fun h c => congrArg (fun x : Paper.Overlap => (x:ℝ)) (W.clock_initial h c))
    hF L hL (fun h σ => hbound (h,σ)) u hu

theorem hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_selected_source
    (hn : 0<n) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1)
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    (u : ℝ) (hu : u∈Icc (0:ℝ) 1) :
    HasDerivWithinAt (followupCavityGeneratedObservedRawForestHistoryExpectation β ρ hβ hρ μ a W M F)
      ((followupCavityAlpha n β ρ/2)*cavityGeneratedObservedRawStreamingStepSelectedSourceIntegral
        (followupCavitySpinModel n β ρ hβ hρ u hu) μ a W M F)
      (Icc (0:ℝ) 1) u := by
  have hd := hasDerivWithinAt_cavityGeneratedObservedRawStreamingStep_raw_source
    hn β ρ hβ hρ μ a ha hμ W M F hF L hL hbound u hu
  rw [cavityGeneratedObservedRawStreamingStep_source_six_eq _ μ a ha hμ W M F] at hd
  exact hd

end QuantitativeFollowup
