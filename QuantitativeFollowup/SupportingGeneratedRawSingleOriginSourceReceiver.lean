module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginSourceReceiverMeasurable

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

theorem cavityGeneratedObservedRawSingleOrigin_originalFresh_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z ∈ cavityGeneratedObservedRawSingleOriginChartEvent W c γ) :
    (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)) := by
  have ho : cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 =
      cavityGeneratedObservedRawChartOrigin (W.component c) γ
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) := by
    have he := cavityGeneratedObservedRawForestSelectionOrigin_eq_chart W c z.2
    have hclass : cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2=γ := hz.1
    rw [hclass] at he
    exact he
  have ht : cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z =
      cavityGeneratedObservedRawChartClock (W.component c) γ z.1
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) := by
    have he := cavityGeneratedObservedRawOriginSelectionClock_eq_chart (W.component c) z
    have hclass : cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2=γ := hz.1
    rw [hclass] at he
    exact he
  rw [ho,ht]
  exact cavityGeneratedObservedRawSingleOrigin_originalFresh_receiver D μ a W c γ F i z.1
    (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) hz.2.2

theorem cavityGeneratedObservedRawSingleOrigin_current_event_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))
    (hz : z ∈ cavityGeneratedObservedRawSingleOriginChartEvent W c γ) :
    (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree))) =
    cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)) := by
  have ho : cavityGeneratedOriginSelectionOrigin (W.tree c) z.2 =
      cavityGeneratedObservedRawChartOrigin (W.component c) γ
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) := by
    have he := cavityGeneratedObservedRawForestSelectionOrigin_eq_chart W c z.2
    have hclass : cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2=γ := hz.1
    rw [hclass] at he
    exact he
  have ht : cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z =
      cavityGeneratedObservedRawChartClock (W.component c) γ z.1
        (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) := by
    have he := cavityGeneratedObservedRawOriginSelectionClock_eq_chart (W.component c) z
    have hclass : cavityGeneratedObservedRawOriginPayloadChart (W.component c) z.2=γ := hz.1
    rw [hclass] at he
    exact he
  rw [ho,ht]
  exact cavityGeneratedObservedRawSingleOrigin_current_receiver D μ a W c γ F z.1
    (cavityGeneratedObservedRawOriginPayloadFreeClock (W.component c) z.2) hz.2.2

theorem cavityGeneratedObservedRawSingleOrigin_originalFresh_chart_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    (∫H, cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i H
      ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) =
    ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).restrict
        (cavityGeneratedObservedRawSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedObservedRawSingleOriginChartMeasure,cavityGeneratedRawOriginSourceMeasure,integral_map
    (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
    (measurable_cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F hF i).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono
    (fun z hz => (cavityGeneratedObservedRawSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz).symm)

theorem cavityGeneratedObservedRawSingleOrigin_current_chart_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    (∫H, cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
      ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ) =
    ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).restrict
        (cavityGeneratedObservedRawSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedObservedRawSingleOriginChartMeasure,cavityGeneratedRawOriginSourceMeasure,integral_map
    (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
    (measurable_cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F hF).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono
    (fun z hz => (cavityGeneratedObservedRawSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm)

theorem cavityGeneratedObservedRawOriginalFreshChartMeasure_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (i : ObservationLeaf (W.tree c)) :
    (∫H, cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i H
      ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) =
    2 * ∫z, (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.originalFresh i (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).restrict
        (cavityGeneratedObservedRawSingleOriginChartEvent W c γ) := by
  rw [cavityGeneratedObservedRawOriginalFreshChartMeasure,integral_smul_measure,
    cavityGeneratedObservedRawSingleOrigin_originalFresh_chart_receiver D μ a W c M γ F hF i]
  norm_num [smul_eq_mul]

theorem cavityGeneratedObservedRawCurrentChartMeasure_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) :
    (∫H, cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
      ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) =
    ∫z, Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z) *
      (∫σ, nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
      (fun τ => F (z.1,Function.update σ c τ))
      (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree
        (W.clock z.1) :
        Measure (CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)))
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).restrict
        (cavityGeneratedObservedRawSingleOriginChartEvent W c γ) := by
  let ρ : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ≥0∞ :=
    fun H => ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m)))
  have hcdf : Measurable (fun H : CavityGeneratedHistory Paper.Overlap (m+1) =>
      Paper.parisiCDF μ (H (Fin.last m))) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (measurable_pi_apply (Fin.last m)))
  have hρ : Measurable ρ := hcdf.ennreal_ofReal
  have hρfinite : ∀ᵐH ∂cavityGeneratedObservedRawSingleOriginChartMeasure μ a W c M γ, ρ H < ∞ :=
    .of_forall (fun _ => ENNReal.ofReal_lt_top)
  rw [cavityGeneratedObservedRawCurrentChartMeasure,
    integral_withDensity_eq_integral_toReal_smul hρ hρfinite]
  have he (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
      (ρ H).toReal • cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H =
      Paper.parisiCDF μ (H (Fin.last m)) *
        cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H := by
    rw [show ρ H = ENNReal.ofReal (Paper.parisiCDF μ (H (Fin.last m))) from rfl,
      ENNReal.toReal_ofReal (Paper.parisiCDF_nonneg μ _),smul_eq_mul]
  simp_rw [he]
  let g : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ := fun H =>
    Paper.parisiCDF μ (H (Fin.last m)) *
      cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
  have hg : Measurable g :=
    hcdf.mul (measurable_cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F hF)
  have hmap := integral_map
    (μ := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).restrict
      (cavityGeneratedObservedRawSingleOriginChartEvent W c γ))
    (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
    hg.aestronglyMeasurable
  refine Eq.trans hmap ?_
  apply integral_congr_ae
  refine (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono ?_
  intro z hz
  simpa only [g,cavityGeneratedRawOriginAppendedHistory,Fin.snoc_last] using
    congrArg (fun x : ℝ => Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)*x)
      (cavityGeneratedObservedRawSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm

end QuantitativeFollowup
