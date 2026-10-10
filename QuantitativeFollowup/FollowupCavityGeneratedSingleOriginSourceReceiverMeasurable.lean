module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginSourceReceiverPointwise
public import QuantitativeFollowup.FollowupCavityGeneratedForestJointLaw

@[expose] public section

/-! Jointly measurable old-forest observables give genuine measurable
single-origin receiver expectations. The terminal carrier is finite;
the clocks and whole old-terminal projection remain the actual ones. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem prefix_measurable :
    Measurable (cavityGeneratedHistoryPrefix : CavityGeneratedHistory Paper.Overlap (m+1) →
      CavityGeneratedHistory Paper.Overlap m) :=
  cavityGeneratedHistoryPrefix_measurable

private theorem level_measurable (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c)) :
    Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      nativeStreamingOriginLevel (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
        (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m)))) := by
  rcases γ with i | (i | u)
  · exact (W.clockTemplate.clock_continuous c _).measurable.comp prefix_measurable
  · exact measurable_pi_apply (Fin.last m)
  · exact (W.clockTemplate.clock_continuous c _).measurable.comp prefix_measurable

private theorem common_measurable (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (γ : PrintedGeneratedOriginChart (W.component c))
    (i : ObservationLeaf (W.tree c)) :
    Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      nativeStreamingOriginCommonClock (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
        (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
        (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m)))) := by
  classical
  rcases γ with v | (e | u)
  · exact (W.clockTemplate.clock_continuous c _).measurable.comp prefix_measurable
  · change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      if finiteCascadeCommonPathDepth (W.tree c) (observationLeafVertex (W.tree c) i)
          (nativeStreamingEdgeChildVertex (printedGeneratedOriginChartEdge (W.component c) e)) =
          (printedGeneratedOriginChartEdge (W.component c) e).depth
      then H (Fin.last m)
      else W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c
        (finiteCascadeCommonPathDepth (W.tree c) (observationLeafVertex (W.tree c) i)
          (nativeStreamingEdgeChildVertex (printedGeneratedOriginChartEdge (W.component c) e))))
    split_ifs
    · exact measurable_pi_apply (Fin.last m)
    · exact (W.clockTemplate.clock_continuous c _).measurable.comp prefix_measurable
  · exact (W.clockTemplate.clock_continuous c _).measurable.comp prefix_measurable

theorem measurable_cavityGeneratedSingleOriginOriginalFreshTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+1) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedSingleOriginChartForest W c γ .single).depth
        (cavityGeneratedSingleOriginChartForest W c γ .single).tree =>
      cavityGeneratedSingleOriginOriginalFreshTest W c γ F i z.1 z.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro σ
  let z := cavityGeneratedSingleOriginTerminalProjection W c γ .single σ
  have hval : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      F (cavityGeneratedHistoryPrefix H,z.1)) :=
    hF.comp (prefix_measurable.prodMk measurable_const)
  have hclock := common_measurable W c γ i
  change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
    F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginCommonClock (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
        (W.tree c) (.vertex (observationLeafVertex (W.tree c) i))
        (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m))))
      (observationTerminalSpin (W.tree c) i (z.1 c)) z.2)
  exact hval.mul (measurable_const.sub
    (((measurable_subtype_coe.comp hclock).mul_const _).mul_const _))

theorem measurable_cavityGeneratedSingleOriginCurrentTest
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (fun z : CavityGeneratedHistory Paper.Overlap (m+1) ×
      CavityGeneratedForestTerminalSample (n:=n)
        (cavityGeneratedSingleOriginChartForest W c γ .current).depth
        (cavityGeneratedSingleOriginChartForest W c γ .current).tree =>
      cavityGeneratedSingleOriginCurrentTest W c γ F z.1 z.2) := by
  classical
  apply measurable_from_prod_countable_left
  intro σ
  let z := cavityGeneratedSingleOriginTerminalProjection W c γ .current σ
  have hval : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      F (cavityGeneratedHistoryPrefix H,z.1)) :=
    hF.comp (prefix_measurable.prodMk measurable_const)
  have hclock := level_measurable W c γ
  change Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
    F (cavityGeneratedHistoryPrefix H,z.1) * cavitySpinOverlapDefect n
      (nativeStreamingOriginLevel (W.clockTemplate.clock (cavityGeneratedHistoryPrefix H) c)
        (printedGeneratedOriginChartOrigin (W.component c) γ (H (Fin.last m)))) z.2.1 z.2.2)
  exact hval.mul (measurable_const.sub
    (((measurable_subtype_coe.comp hclock).mul_const _).mul_const _))

def cavityGeneratedSingleOriginOriginalFreshExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c)) (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  ∫σ, cavityGeneratedSingleOriginOriginalFreshTest W c γ F i H σ
    ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedSingleOriginChartForest W c γ .single) H

def cavityGeneratedSingleOriginCurrentExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) : ℝ :=
  ∫σ, cavityGeneratedSingleOriginCurrentTest W c γ F H σ
    ∂cavityGeneratedForestTerminalKernel D μ a (cavityGeneratedSingleOriginChartForest W c γ .current) H

theorem measurable_cavityGeneratedSingleOriginOriginalFreshExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    Measurable (cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i) := by
  have hf := (measurable_cavityGeneratedSingleOriginOriginalFreshTest W c γ F hF i).stronglyMeasurable
  exact (hf.integral_kernel_prod_right'
    (κ := cavityGeneratedForestTerminalKernel D μ a
      (cavityGeneratedSingleOriginChartForest W c γ .single))).measurable

theorem measurable_cavityGeneratedSingleOriginCurrentExpectation
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    Measurable (cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F) := by
  have hf := (measurable_cavityGeneratedSingleOriginCurrentTest W c γ F hF).stronglyMeasurable
  exact (hf.integral_kernel_prod_right'
    (κ := cavityGeneratedForestTerminalKernel D μ a
      (cavityGeneratedSingleOriginChartForest W c γ .current))).measurable

theorem cavityGeneratedSingleOriginOriginalFreshTest_abs_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀z, |F z| ≤ C)
    (i : ObservationLeaf (W.tree c)) (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .single).depth
      (cavityGeneratedSingleOriginChartForest W c γ .single).tree) :
    |cavityGeneratedSingleOriginOriginalFreshTest W c γ F i H σ| ≤ 2*C := by
  unfold cavityGeneratedSingleOriginOriginalFreshTest
  dsimp only
  rw [abs_mul]
  exact (mul_le_mul (hF _) (cavitySpinOverlapDefect_abs_le_two n _
    (nativeStreamingOriginCommonClock _ _ _ _).property _ _) (abs_nonneg _) hC).trans_eq (by ring)

theorem cavityGeneratedSingleOriginCurrentTest_abs_le
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀z, |F z| ≤ C)
    (H : CavityGeneratedHistory Paper.Overlap (m+1))
    (σ : CavityGeneratedForestTerminalSample (n:=n)
      (cavityGeneratedSingleOriginChartForest W c γ .current).depth
      (cavityGeneratedSingleOriginChartForest W c γ .current).tree) :
    |cavityGeneratedSingleOriginCurrentTest W c γ F H σ| ≤ 2*C := by
  unfold cavityGeneratedSingleOriginCurrentTest
  dsimp only
  rw [abs_mul]
  exact (mul_le_mul (hF _) (cavitySpinOverlapDefect_abs_le_two n _
    (nativeStreamingOriginLevel _ _).property _ _) (abs_nonneg _) hC).trans_eq (by ring)

theorem cavityGeneratedSingleOriginOriginalFreshExpectation_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀z, |F z| ≤ C)
    (i : ObservationLeaf (W.tree c)) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    |cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H| ≤ 2*C := by
  have he := norm_integral_le_of_norm_le_const
    (μ := cavityGeneratedForestTerminalKernel D μ a
      (cavityGeneratedSingleOriginChartForest W c γ .single) H)
    (f := cavityGeneratedSingleOriginOriginalFreshTest W c γ F i H) (C := 2*C)
    (.of_forall (fun σ => by simpa only [Real.norm_eq_abs] using
      cavityGeneratedSingleOriginOriginalFreshTest_abs_le W c γ F C hC hF i H σ))
  simpa only [cavityGeneratedSingleOriginOriginalFreshExpectation,Real.norm_eq_abs,
    probReal_univ,mul_one] using he

theorem cavityGeneratedSingleOriginCurrentExpectation_abs_le
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (hF : ∀z, |F z| ≤ C)
    (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    |cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H| ≤ 2*C := by
  have he := norm_integral_le_of_norm_le_const
    (μ := cavityGeneratedForestTerminalKernel D μ a
      (cavityGeneratedSingleOriginChartForest W c γ .current) H)
    (f := cavityGeneratedSingleOriginCurrentTest W c γ F H) (C := 2*C)
    (.of_forall (fun σ => by simpa only [Real.norm_eq_abs] using
      cavityGeneratedSingleOriginCurrentTest_abs_le W c γ F C hC hF H σ))
  simpa only [cavityGeneratedSingleOriginCurrentExpectation,Real.norm_eq_abs,
    probReal_univ,mul_one] using he

end QuantitativeFollowup
