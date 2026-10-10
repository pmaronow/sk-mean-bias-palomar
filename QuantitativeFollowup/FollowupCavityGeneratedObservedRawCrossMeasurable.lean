module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossProjection
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingKernel

@[expose] public section

/-! The actual raw cross successor retains the joint old observable.
Its history-dependent clocks need only be measurable: the fresh spin
coordinates are finite, and the true forest terminal law is a kernel. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

private theorem measurable_fresh_defect
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree =>
      cavityGeneratedObservedRawCrossFreshDefect W c γ δ k z.1 z.2) := by
  apply measurable_from_prod_countable_left
  intro σ
  let V := W.reindex (fun i => i.castSucc.castSucc)
  let U := cavityGeneratedObservedRawCrossComponent (W.component c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let τ := (cavityGeneratedObservedRawForestReplacementSelectedEquiv (n:=n) V c U).symm (σ c)
  let i := cavityGeneratedRawCrossFirstLeaf (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  let j := cavityGeneratedRawCrossSecondLeaf (W.tree c)
    (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
  change Measurable (fun H => cavitySpinOverlapDefect n (U.clock H (observationCommonLevel U.tree i j))
    (observationTerminalSpin U.tree i τ) (observationTerminalSpin U.tree j τ))
  exact (continuous_cavitySpinOverlapDefect_clock (fun r : Paper.Overlap => r) continuous_id
    (observationTerminalSpin U.tree i τ) (observationTerminalSpin U.tree j τ)).measurable.comp
      (U.measurable_clock (observationCommonLevel U.tree i j))

private theorem abs_fresh_defect_le_two
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    |cavityGeneratedObservedRawCrossFreshDefect W c γ δ k H σ|≤2 := by
  unfold cavityGeneratedObservedRawCrossFreshDefect
  exact cavitySpinOverlapDefect_abs_le_two n _ (by exact (Subtype.property _)) _ _

theorem measurable_cavityGeneratedObservedRawCrossTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+2) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree =>
      cavityGeneratedObservedRawCrossTest W c γ δ k F z.1 z.2) :=
  (hF.comp (measurable_cavityGeneratedObservedRawCrossBaseMap W c γ δ k)).mul
    (measurable_fresh_defect W c γ δ k)

theorem abs_cavityGeneratedObservedRawCrossTest_le
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L)
    (H : CavityGeneratedHistory Paper.Overlap (m+2))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree) :
    |cavityGeneratedObservedRawCrossTest W c γ δ k F H σ|≤2*L := by
  rw [cavityGeneratedObservedRawCrossTest,abs_mul]
  exact (mul_le_mul (hbound _) (abs_fresh_defect_le_two W c γ δ k H σ)
    (abs_nonneg _) hL).trans_eq (by ring)

def cavityGeneratedObservedRawCrossChartExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) : ℝ :=
  ∫σ, cavityGeneratedObservedRawCrossTest W c γ δ k F H σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
      (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree
      ((cavityGeneratedObservedRawCrossChartForest W c γ δ k).clock H) : Measure _)

theorem measurable_cavityGeneratedObservedRawCrossChartExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F) := by
  let V := cavityGeneratedObservedRawCrossChartForest W c γ δ k
  have hi := (measurable_cavityGeneratedObservedRawCrossTest W c γ δ k F hF).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedRawForestTerminalKernel D μ a V.depth V.tree V.clock V.measurable_clock V.clock_antitone)
  convert hi.measurable using 1
  funext H
  rw [cavityGeneratedRawForestTerminalKernel_apply]
  rfl

theorem abs_cavityGeneratedObservedRawCrossChartExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L)
    (H : CavityGeneratedHistory Paper.Overlap (m+2)) :
    |cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F H|≤2*L := by
  simpa only [cavityGeneratedObservedRawCrossChartExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).depth
        (cavityGeneratedObservedRawCrossChartForest W c γ δ k).tree
        ((cavityGeneratedObservedRawCrossChartForest W c γ δ k).clock H) : Measure _))
      (f:=cavityGeneratedObservedRawCrossTest W c γ δ k F H) (C:=2*L)
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using
        abs_cavityGeneratedObservedRawCrossTest_le W c γ δ k F L hL hbound H σ)

end QuantitativeFollowup
