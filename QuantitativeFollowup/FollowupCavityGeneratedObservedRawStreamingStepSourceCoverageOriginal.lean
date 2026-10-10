module
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacementBasis
public import QuantitativeFollowup.FollowupCavityGeneratedRawForestHistoryStreamingKernel
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageOriginal

@[expose] public section

/-! The original-pair successor uses the genuine original whole-forest
test. Resampling the selected component averages its unused copy to one;
the other components and their joint terminal test remain intact. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

def cavityGeneratedObservedRawStreamingOriginalTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  F (h,σ)*(if i=k then 0 else cavitySpinOverlapDefect n
    (W.clock h c (observationCommonLevel (W.tree c) i k))
    (observationTerminalSpin (W.tree c) i (σ c)) (observationTerminalSpin (W.tree c) k (σ c)))

theorem measurable_cavityGeneratedObservedRawStreamingOriginalTest
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
        cavityGeneratedObservedRawStreamingOriginalTest W c i k F z.1 z.2) := by
  have hd : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
      if i=k then (0:ℝ) else cavitySpinOverlapDefect n
        (W.clock z.1 c (observationCommonLevel (W.tree c) i k))
        (observationTerminalSpin (W.tree c) i (z.2 c))
        (observationTerminalSpin (W.tree c) k (z.2 c))) := by
    apply measurable_from_prod_countable_left
    intro σ
    by_cases hik : i=k
    · simpa only [if_pos hik] using (measurable_const (a:=(0:ℝ)))
    · simpa only [if_neg hik,Function.comp_def] using
        (continuous_cavitySpinOverlapDefect_clock (fun r : Paper.Overlap => r) continuous_id
          (observationTerminalSpin (W.tree c) i (σ c))
          (observationTerminalSpin (W.tree c) k (σ c))).measurable.comp
            (W.measurable_clock c (observationCommonLevel (W.tree c) i k))
  exact hF.mul hd

theorem abs_cavityGeneratedObservedRawStreamingOriginalTest_le
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F (h,σ)|≤C)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedObservedRawStreamingOriginalTest W c i k F h σ|≤2*C := by
  by_cases hik : i=k
  · simp only [cavityGeneratedObservedRawStreamingOriginalTest,if_pos hik,mul_zero,abs_zero]
    positivity
  · simp only [cavityGeneratedObservedRawStreamingOriginalTest,if_neg hik,abs_mul]
    exact (mul_le_mul (hF h σ)
      (cavitySpinOverlapDefect_abs_le_two n _ (by exact (W.clock h c _).property) _ _)
      (abs_nonneg _) hC).trans_eq (by ring)

def cavityGeneratedObservedRawStreamingOriginalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,cavityGeneratedObservedRawStreamingOriginalTest W c i k F h σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clock h) : Measure _)

theorem measurable_cavityGeneratedObservedRawStreamingOriginalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F) := by
  have he := (measurable_cavityGeneratedObservedRawStreamingOriginalTest W c i k F hF).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock W.measurable_clock W.clock_antitone)
  convert he.measurable using 1
  funext h
  rw [cavityGeneratedRawForestTerminalKernel_apply]
  rfl

theorem cavityGeneratedObservedRawStreamingOriginal_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ)) (.original i k)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _)) =
      cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h := by
  let G := cavityGeneratedObservedRawStreamingOriginalTest W c i k F h
  have he σ : nativeStreamingPatternMoment D μ a (W.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ)) (.original i k) =
      nativeStreamingOldTerminalExpectation D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree G c σ) := by
    by_cases hik : i=k
    · simp only [nativeStreamingPatternMoment,if_pos hik,nativeStreamingOldTerminalExpectation,
        cavityGeneratedForestPartialTerminalTest,G,cavityGeneratedObservedRawStreamingOriginalTest,mul_zero,integral_zero]
    · simp only [nativeStreamingPatternMoment,if_neg hik,nativeStreamingOldTerminalExpectation]
      apply integral_congr_ae (.of_forall fun z => ?_)
      simp only [cavityGeneratedForestPartialTerminalTest,G,cavityGeneratedObservedRawStreamingOriginalTest,
        if_neg hik,Function.update_self,observationTerminalSpin_record]
      congr 2
      apply Prod.ext
      · rfl
      · funext j
        by_cases hj : j=c
        · subst j
          simp only [Function.update_self]
        · simp [Function.update,hj]
  calc
    _ = ∫σ,nativeStreamingOldTerminalExpectation D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree G c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clock h) : Measure _) := integral_congr_ae (.of_forall he)
    _ = _ := cavityGeneratedNativeForest_component_resampling D μ a W.depth W.tree
      (W.clock h) G c

theorem abs_cavityGeneratedObservedRawStreamingOriginalExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F (h,σ)|≤C)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    |cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h|≤2*C := by
  simpa only [cavityGeneratedObservedRawStreamingOriginalExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock h) : Measure _))
      (f:=cavityGeneratedObservedRawStreamingOriginalTest W c i k F h) (C:=2*C)
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using
        abs_cavityGeneratedObservedRawStreamingOriginalTest_le W c i k F C hC hF h σ)

end QuantitativeFollowup
