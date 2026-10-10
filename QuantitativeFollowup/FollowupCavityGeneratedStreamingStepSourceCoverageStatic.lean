module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageOriginal
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageAveraging
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSix

@[expose] public section

/-! One actual component source expands into the six genuine selected
payload integrals, averaged against the whole untouched forest law.
The normalizer is an independent component and the old diagonal remains
zero. This is a source identity, before chart replacement. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedForestPartialTerminalTest_fin_apply
    {s : ℕ} (J : Fin s → ℕ) (T : (i : Fin s) → FiniteTerminalGenealogy (J i))
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ)
    (c : Fin s) (σ : CavityGeneratedForestTerminalSample (n:=n) J T)
    (τ : TerminalSpins (Configuration (n+1)) (T c)) :
    cavityGeneratedForestPartialTerminalTest J T F c σ τ = F (Function.update σ c τ) := by
  unfold cavityGeneratedForestPartialTerminalTest
  congr 1
  funext d
  by_cases hd : d=c
  · subst d
    simp only [Function.update_self]
  · simp [Function.update,hd]

theorem cavityGeneratedNativeForest_normalizer_partial_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) (l : Paper.Overlap) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree F c σ) (.normalizer l)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _)) =
    (∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) : Measure _))*nativeStreamingFreshDefectMoment D μ a l := by
  simp_rw [nativeStreamingPatternMoment_normalizer_independent,
    ←nativeStreamingFreshDefectMoment_eq_fresh D μ a l]
  rw [integral_mul_const,cavityGeneratedNativeForest_component_resampling]

def cavityGeneratedStreamingComponentSelectedSource
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  let q : Fin W.componentCount → ℕ → Paper.Overlap := W.clockTemplate.clock h
  let N : Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :=
    cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree q
  let L := cavityGeneratedOriginSelectionMeasure μ a (q c) (W.tree c) a
  let P := fun σ => cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h, τ)) c σ
  (∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
    cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h) +
  (-2*∑i : ObservationLeaf (W.tree c),∫g,∫σ,
    cavityGeneratedSelectedOriginalFreshPayload D μ a (q c) (W.tree c) (P σ) i g ∂N ∂L) +
  (∫z,∫σ,cavityGeneratedSelectedCrossPayload D μ a (q c) (W.tree c) (P σ) z ∂N ∂L.prod L) +
  (∫g,∫σ,cavityGeneratedSelectedCurrentPayload D μ a (q c) (W.tree c) (P σ) g ∂N ∂L) +
  (∫z,∫σ,cavityGeneratedSelectedFuturePayload D μ a (q c) (W.tree c) (P σ) z
    ∂N ∂L.prod (parisiFreeMeasure μ a)) +
  a*(∫σ,F (h,σ) ∂N)*(∫l,nativeStreamingFreshDefectMoment D μ a l ∂parisiFreeMeasure μ a)

theorem cavityGeneratedStreamingComponent_source_six_eq
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (∫σ,nativeStreamingSourceSixBracket D μ a (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h, τ)) c σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _)) =
    cavityGeneratedStreamingComponentSelectedSource D μ a W c F h := by
  let q : Fin W.componentCount → ℕ → Paper.Overlap := W.clockTemplate.clock h
  let G := cavityGeneratedForestAveragedPartialTerminalTest D μ a W.depth W.tree q
    (fun τ => F (h, τ)) c
  have hq d : Antitone (q d) := antitone_nat_of_succ_le (W.clockTemplate.clock_step_le h d)
  rw [cavityGeneratedNativeForest_source_partial_integral_eq_average D μ a W.depth W.tree q hq]
  rw [nativeStreamingSourceSixBracket_eq_selected_payload D μ a ha hμ (q c) (hq c)
    (W.clockTemplate.clock_terminal h c) (W.clockTemplate.clock_initial h c)]
  have horig (i k : ObservationLeaf (W.tree c)) :
      nativeStreamingPatternMoment D μ a (q c) (W.tree c) G (.original i k) =
      cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h := by
    rw [←cavityGeneratedNativeForest_pattern_partial_integral_eq_average D μ a W.depth W.tree q
      (fun τ => F (h, τ)) c (.original i k)]
    have htest (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
        cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ => F (h, τ)) c σ =
          (fun τ => F (h, Function.update σ c τ)) := by
      funext τ
      exact cavityGeneratedForestPartialTerminalTest_fin_apply W.depth W.tree
        (fun τ => F (h, τ)) c σ τ
    simp_rw [htest]
    exact cavityGeneratedStreamingOriginal_source_receiver D μ a W c i k F h
  have hnormal (l : Paper.Overlap) : nativeStreamingPatternMoment D μ a (q c) (W.tree c) G
      (.normalizer l) =
      (∫σ,F (h,σ) ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree q : Measure _))*
        nativeStreamingFreshDefectMoment D μ a l := by
    rw [←cavityGeneratedNativeForest_pattern_partial_integral_eq_average D μ a W.depth W.tree q
      (fun τ => F (h, τ)) c (.normalizer l)]
    exact cavityGeneratedNativeForest_normalizer_partial_receiver D μ a W c (fun τ => F (h, τ)) h l
  unfold cavityGeneratedSelectedSourceSixBracket cavityGeneratedStreamingComponentSelectedSource
  change nativeStreamingSourceOriginalTerm D μ a (q c) (W.tree c) G + _ + _ + _ + _ + _ = _
  unfold nativeStreamingSourceOriginalTerm
  simp_rw [horig]
  rw [show (fun l => nativeStreamingPatternMoment D μ a (q c) (W.tree c) G
      (.normalizer l)) =
      (fun l => (∫σ, F (h,σ) ∂(cavityGeneratedNativeForestTerminalProbability D μ a
        W.depth W.tree q : Measure _))*nativeStreamingFreshDefectMoment D μ a l)
      from funext hnormal]
  rw [integral_const_mul]
  simp_rw [←cavityGeneratedNativeForest_originalFreshPayload_average D μ a W.depth W.tree q
    (fun τ => F (h, τ)) c,
    ←cavityGeneratedNativeForest_crossPayload_average D μ a W.depth W.tree q (fun τ => F (h, τ)) c,
    ←cavityGeneratedNativeForest_currentPayload_average D μ a W.depth W.tree q (fun τ => F (h, τ)) c,
    ←cavityGeneratedNativeForest_futurePayload_average D μ a W.depth W.tree q (fun τ => F (h, τ)) c]
  ring

end QuantitativeFollowup
