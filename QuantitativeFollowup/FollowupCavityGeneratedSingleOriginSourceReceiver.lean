module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginSourceReceiverMeasurable
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginWeights

@[expose] public section

/-! Actual single-origin chart measures receive the original/fresh and
current source callbacks. Both integral identities retain the whole old
forest terminal test and its original history. The factor two and CDF
are the genuine exterior source coefficients. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedSingleOrigin_originalFresh_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z ∈ cavityGeneratedSingleOriginChartEvent W c γ) :
    (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)) := by
  have ho : cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 =
      printedGeneratedOriginChartOrigin (W.component c) γ
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rw [cavityGeneratedOriginSelectionOrigin_eq_chart,hz.1]
  have ht : cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c) γ z.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hz.1]
  rw [ho,ht]
  exact cavityGeneratedSingleOrigin_originalFresh_receiver D μ a W c γ F i z.1
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) hz.2.1 hz.2.2

theorem cavityGeneratedSingleOrigin_current_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z ∈ cavityGeneratedSingleOriginChartEvent W c γ) :
    (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z)) := by
  have ho : cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 =
      printedGeneratedOriginChartOrigin (W.component c) γ
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rw [cavityGeneratedOriginSelectionOrigin_eq_chart,hz.1]
  have ht : cavityGeneratedOriginSelectionClock W c z =
      printedGeneratedOriginChartClock (W.component c) γ z.1
        (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) := by
    rw [cavityGeneratedOriginSelectionClock_eq_chart,hz.1]
  rw [ho,ht]
  exact cavityGeneratedSingleOrigin_current_receiver D μ a W c γ F z.1
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) hz.2.1 hz.2.2

theorem cavityGeneratedSingleOrigin_originalFresh_chart_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    (∫H, cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H
      ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ) =
    ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
        (cavityGeneratedSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedSingleOriginChartMeasure,integral_map
    (cavityGeneratedSingleOriginChart_append_measurable W c).aemeasurable
    (measurable_cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F hF i).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono
    (fun z hz => (cavityGeneratedSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz).symm)

theorem cavityGeneratedSingleOrigin_current_chart_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    (∫H, cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
      ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ) =
    ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
        (cavityGeneratedSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedSingleOriginChartMeasure,integral_map
    (cavityGeneratedSingleOriginChart_append_measurable W c).aemeasurable
    (measurable_cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F hF).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono
    (fun z hz => (cavityGeneratedSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm)

theorem cavityGeneratedOriginalFreshChartMeasure_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    (∫H, cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H
      ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) =
    2 * ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
        (cavityGeneratedSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedOriginalFreshChartMeasure,integral_smul_measure,
    cavityGeneratedSingleOrigin_originalFresh_chart_receiver D μ a W c M γ F hF i]
  norm_num [smul_eq_mul]

theorem cavityGeneratedCurrentChartMeasure_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : PrintedGeneratedOriginChart (W.component c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    (∫H, cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
      ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) =
    ∫z, Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z) *
      (∫σ, nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clockTemplate.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
        (cavityGeneratedSingleOriginChartEvent W c γ) := by
  let ρ : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ≥0∞ :=
    fun H => ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m)))
  have hcdf : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      Paper.parisiCDF μ (H (Fin.last m))) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last m)))
  have hρ : Measurable ρ := hcdf.ennreal_ofReal
  have hρfinite : ∀ᵐH ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ, ρ H < ∞ :=
    .of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [cavityGeneratedCurrentChartMeasure,
    integral_withDensity_eq_integral_toReal_smul hρ hρfinite]
  have he (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
      (ρ H).toReal • cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H =
      Paper.parisiCDF μ (H (Fin.last m)) *
        cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H := by
    rw [show ρ H = ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m))) from rfl,
      ENNReal.toReal_ofReal (Paper.parisiCDF_nonneg μ _),smul_eq_mul]
  simp_rw [he]
  let g : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ := fun H =>
    Paper.parisiCDF μ (H (Fin.last m)) *
      cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
  have hg : Measurable g :=
    hcdf.mul (measurable_cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F hF)
  have hmap := integral_map
    (μ := (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).restrict
      (cavityGeneratedSingleOriginChartEvent W c γ))
    (cavityGeneratedSingleOriginChart_append_measurable W c).aemeasurable
    hg.aestronglyMeasurable
  refine Eq.trans hmap ?_
  apply integral_congr_ae
  refine (ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono ?_
  intro z hz
  simpa only [g,Fin.snoc_last] using
    congrArg (fun x : ℝ => Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)*x)
      (cavityGeneratedSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm

end QuantitativeFollowup
