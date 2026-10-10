module
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacementBasis
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

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

private theorem old_terminal_basis {j : ℕ}
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy j)
    (G : TerminalSpins (Configuration (n+1)) T → ℝ) :
    nativeStreamingOldTerminalExpectation D μ a q T G =
      ∑τ,G τ*nativeStreamingOldTerminalExpectation D μ a q T
        (cavityGeneratedTerminalSingletonTest τ) := by
  have hi τ : Integrable (fun z => G τ*cavityGeneratedTerminalSingletonTest τ
      (finiteCascadeRecordTerminalSpins T z.2))
      (anisotropicRecordedProfileTreeLaw D μ a q T) := by
    apply (integrable_const |G τ|).mono'
      (((measurable_of_finite (fun σ => G τ*cavityGeneratedTerminalSingletonTest τ σ)).comp
        ((measurable_finiteCascadeRecordTerminalSpins T).comp measurable_snd)).aestronglyMeasurable)
    exact .of_forall fun z => by
      change |G τ*cavityGeneratedTerminalSingletonTest τ
        (finiteCascadeRecordTerminalSpins T z.2)|≤|G τ|
      by_cases he : finiteCascadeRecordTerminalSpins T z.2=τ
      · simp [cavityGeneratedTerminalSingletonTest,he]
      · simp [cavityGeneratedTerminalSingletonTest,he]
  unfold nativeStreamingOldTerminalExpectation
  calc
    _ = ∫z,∑τ,G τ*cavityGeneratedTerminalSingletonTest τ
        (finiteCascadeRecordTerminalSpins T z.2) ∂anisotropicRecordedProfileTreeLaw D μ a q T := by
      apply integral_congr_ae (.of_forall fun z => ?_)
      simp [cavityGeneratedTerminalSingletonTest,eq_comm]
    _ = ∑τ,∫z,G τ*cavityGeneratedTerminalSingletonTest τ
        (finiteCascadeRecordTerminalSpins T z.2) ∂anisotropicRecordedProfileTreeLaw D μ a q T :=
      integral_finsetSum _ (fun τ _ => hi τ)
    _ = _ := by simp_rw [integral_const_mul]

theorem cavityGeneratedNativeForest_component_resampling
    {I : Type*} [Fintype I]
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (J : I → ℕ) (T : (i : I) → FiniteTerminalGenealogy (J i))
    (q : I → ℕ → Paper.Overlap)
    (F : CavityGeneratedForestTerminalSample (n:=n) J T → ℝ) (c : I) :
    (∫σ,nativeStreamingOldTerminalExpectation D μ a (q c) (T c)
      (cavityGeneratedForestPartialTerminalTest J T F c σ)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _)) =
      ∫σ,F σ ∂(cavityGeneratedNativeForestTerminalProbability D μ a J T q : Measure _) := by
  rw [cavityGeneratedNativeForest_partial_functional_basis D μ a J T q F c
    (nativeStreamingOldTerminalExpectation D μ a (q c) (T c))
    (old_terminal_basis D μ a (q c) (T c)),cavityGeneratedNativeForest_terminal_basis]
  apply Finset.sum_congr rfl
  intro σ _
  rw [←Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  ring

def cavityGeneratedStreamingOriginalTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) : ℝ :=
  F (h,σ)*(if i=k then 0 else cavitySpinOverlapDefect n
    (W.clockTemplate.clock h c (observationCommonLevel (W.tree c) i k))
    (observationTerminalSpin (W.tree c) i (σ c)) (observationTerminalSpin (W.tree c) k (σ c)))

theorem measurable_cavityGeneratedStreamingOriginalTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
        cavityGeneratedStreamingOriginalTest W c i k F z.1 z.2) := by
  have hd : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree =>
      if i=k then (0:ℝ) else cavitySpinOverlapDefect n
        (W.clockTemplate.clock z.1 c (observationCommonLevel (W.tree c) i k))
        (observationTerminalSpin (W.tree c) i (z.2 c))
        (observationTerminalSpin (W.tree c) k (z.2 c))) := by
    apply measurable_from_prod_countable_left
    intro σ
    by_cases hik : i=k
    · simpa only [if_pos hik] using (measurable_const (a:=(0:ℝ)))
    · simpa only [if_neg hik] using (continuous_cavitySpinOverlapDefect_clock
        (fun h => W.clockTemplate.clock h c (observationCommonLevel (W.tree c) i k))
        (W.clockTemplate.clock_continuous c _) (observationTerminalSpin (W.tree c) i (σ c))
        (observationTerminalSpin (W.tree c) k (σ c))).measurable
  exact hF.mul hd

theorem abs_cavityGeneratedStreamingOriginalTest_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F (h,σ)|≤C)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    |cavityGeneratedStreamingOriginalTest W c i k F h σ|≤2*C := by
  by_cases hik : i=k
  · simp only [cavityGeneratedStreamingOriginalTest,if_pos hik,mul_zero,abs_zero]
    positivity
  · simp only [cavityGeneratedStreamingOriginalTest,if_neg hik,abs_mul]
    exact (mul_le_mul (hF h σ)
      (cavitySpinOverlapDefect_abs_le_two n _ (by exact (W.clockTemplate.clock h c _).property) _ _)
      (abs_nonneg _) hC).trans_eq (by ring)

def cavityGeneratedStreamingOriginalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) : ℝ :=
  ∫σ,cavityGeneratedStreamingOriginalTest W c i k F h σ
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
      (W.clockTemplate.clock h) : Measure _)

theorem measurable_cavityGeneratedStreamingOriginalExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedStreamingOriginalExpectation D μ a W c i k F) := by
  have he := (measurable_cavityGeneratedStreamingOriginalTest W c i k F hF).stronglyMeasurable.integral_kernel_prod_right'
    (κ:=cavityGeneratedForestTerminalKernel D μ a W)
  convert he.measurable using 1
  funext h
  rw [cavityGeneratedForestTerminalKernel_apply]
  rfl

theorem cavityGeneratedStreamingOriginal_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (∫σ,nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ)) (.original i k)
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _)) =
      cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h := by
  let G := cavityGeneratedStreamingOriginalTest W c i k F h
  have he σ : nativeStreamingPatternMoment D μ a (W.clockTemplate.clock h c) (W.tree c)
      (fun τ => F (h,Function.update σ c τ)) (.original i k) =
      nativeStreamingOldTerminalExpectation D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree G c σ) := by
    by_cases hik : i=k
    · simp only [nativeStreamingPatternMoment,if_pos hik,nativeStreamingOldTerminalExpectation,
        cavityGeneratedForestPartialTerminalTest,G,cavityGeneratedStreamingOriginalTest,mul_zero,integral_zero]
    · simp only [nativeStreamingPatternMoment,if_neg hik,nativeStreamingOldTerminalExpectation]
      apply integral_congr_ae (.of_forall fun z => ?_)
      simp only [cavityGeneratedForestPartialTerminalTest,G,cavityGeneratedStreamingOriginalTest,
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
    _ = ∫σ,nativeStreamingOldTerminalExpectation D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree G c σ)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
          (W.clockTemplate.clock h) : Measure _) := integral_congr_ae (.of_forall he)
    _ = _ := cavityGeneratedNativeForest_component_resampling D μ a W.depth W.tree
      (W.clockTemplate.clock h) G c

theorem abs_cavityGeneratedStreamingOriginalExpectation_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (i k : ObservationLeaf (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀h σ,|F (h,σ)|≤C)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    |cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h|≤2*C := by
  simpa only [cavityGeneratedStreamingOriginalExpectation,Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const
      (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock h) : Measure _))
      (f:=cavityGeneratedStreamingOriginalTest W c i k F h) (C:=2*C)
      (.of_forall fun σ => by simpa only [Real.norm_eq_abs] using
        abs_cavityGeneratedStreamingOriginalTest_le W c i k F C hC hF h σ)

end QuantitativeFollowup
