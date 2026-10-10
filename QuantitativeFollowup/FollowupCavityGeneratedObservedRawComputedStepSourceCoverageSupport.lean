module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverageOriginal
public import QuantitativeFollowup.SupportingGeneratedObservedRawNormalizerSourceReceiver

@[expose] public section

/-! The original terms and the independent normalizer are integrable
under a finite history measure. Bounds come from the genuine whole
forest probability and the original joint test. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def cavityGeneratedObservedRawStreamingBaseExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ, F (h,σ) ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
    (W.clock h) : Measure _)

theorem measurable_cavityGeneratedObservedRawStreamingBaseExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F) := by
  have hi := hF.stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock
      W.measurable_clock W.clock_antitone)
  convert hi.measurable using 1
  funext h
  rw [cavityGeneratedRawForestTerminalKernel_apply]
  rfl

theorem abs_cavityGeneratedObservedRawStreamingBaseExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (L : ℝ) (hbound : ∀z, |F z|≤L) (h : CavityGeneratedHistory Paper.Overlap m) :
    |cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F h|≤L := by
  simpa only [cavityGeneratedObservedRawStreamingBaseExpectation,Real.norm_eq_abs,
    probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _)) (f:=fun σ => F (h,σ)) (C:=L)
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using hbound (h,σ))

theorem integrable_cavityGeneratedObservedRawStreamingBaseExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hbound : ∀z, |F z|≤L) :
    Integrable (cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F) M :=
  (integrable_const L).mono'
    (measurable_cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F hF).aestronglyMeasurable
    (.of_forall fun h => by simpa only [Real.norm_eq_abs] using
      abs_cavityGeneratedObservedRawStreamingBaseExpectation_le D μ a W F L hbound h)

theorem integrable_cavityGeneratedObservedRawStreamingOriginalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L) :
    Integrable (cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F) M := by
  refine (integrable_const (2*L)).mono'
    (measurable_cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F hF).aestronglyMeasurable ?_
  exact .of_forall fun h => by
    have hh := abs_cavityGeneratedObservedRawStreamingOriginalExpectation_le D μ a W c i k F L hL
      (fun h σ => hbound (h,σ)) h
    simpa only [Real.norm_eq_abs] using hh

theorem integrable_cavityGeneratedObservedRawStreamingNormalizerSource
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hbound : ∀z, |F z|≤L) :
    Integrable (fun h => a * cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F h *
      (∫l, nativeStreamingFreshDefectMoment D μ a l ∂parisiFreeMeasure μ a)) M :=
  ((integrable_cavityGeneratedObservedRawStreamingBaseExpectation D μ a W M F hF L hbound).const_mul a).mul_const _

end QuantitativeFollowup
