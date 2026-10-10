module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageSupport
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginSourceReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginChartCoverage
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingPatternValueBounds

@[expose] public section

/-! The true single-origin chart partition covers the selected source.
Only actual original Ioc-supported draws are unmasked. The original/fresh
factor two and current CDF are the already computed chart measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

private theorem chart_integrable_sum
    {X K : Type*} [MeasurableSpace X] [Fintype K]
    (N : Measure X) [IsFiniteMeasure N] (E : K → Set X)
    (hE : ∀k,MeasurableSet (E k)) (hd : Pairwise (Disjoint on E))
    (hc : ∀ᵐx ∂N,∃k,x∈E k) (Φ : X → ℝ) (Ψ : K → X → ℝ)
    (hΨ : ∀k,Measurable (Ψ k)) (B : ℝ) (hb : ∀k x,|Ψ k x|≤B)
    (he : ∀k,Φ=ᵐ[N.restrict (E k)] Ψ k) :
    Integrable Φ N ∧ (∑k,∫x,Φ x ∂N.restrict (E k))=∫x,Φ x ∂N := by
  have hi k : Integrable Φ (N.restrict (E k)) :=
    ((integrable_const B).mono' (hΨ k).aestronglyMeasurable
      (.of_forall fun x=>by simpa only [Real.norm_eq_abs] using hb k x)).congr (he k).symm
  have hN := finiteMeasureChartPartition_sum_restrict N E hE hd hc
  have hf : Integrable Φ N := by
    rw [←hN]
    exact integrable_finsetSum_measure.mpr (fun k _=>hi k)
  refine ⟨hf,?_⟩
  calc
    (∑k,∫x,Φ x ∂N.restrict (E k)) =
        ∫x,Φ x ∂(∑k,N.restrict (E k)) :=
      (integral_finsetSum_measure (fun k _=>hi k)).symm
    _ = ∫x,Φ x ∂N := by rw [hN]

def cavityGeneratedStreamingOriginalFreshSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) : ℝ :=
  ∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
    (fun τ=>F (z.1,Function.update σ c τ)) i z.2 ∂cavityGeneratedForestTerminalKernel D μ a W z.1

def cavityGeneratedStreamingCurrentSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) : ℝ :=
  ∫σ,cavityGeneratedSelectedCurrentPayload D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
    (fun τ=>F (z.1,Function.update σ c τ)) z.2 ∂cavityGeneratedForestTerminalKernel D μ a W z.1

theorem cavityGeneratedStreamingOriginalFresh_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C)
    (i : ObservationLeaf (W.tree c)) :
    Integrable (cavityGeneratedStreamingOriginalFreshSourceValue D μ a W c F i)
      (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ∧
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H
        ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) =
    2*∫z,cavityGeneratedStreamingOriginalFreshSourceValue D μ a W c F i z
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let N := M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c
  let A := cavityGeneratedStreamingOriginalFreshSourceValue D μ a W c F i
  let E := cavityGeneratedSingleOriginChartEvent W c
  let Ψ : PrintedGeneratedOriginChart (W.component c) →
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) → ℝ :=
    fun γ z=>cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i
    (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z))
  have hm γ : Measurable (Ψ γ) :=
    (measurable_cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F hF i).comp
      (cavityGeneratedSingleOriginChart_append_measurable W c)
  have hb γ z : |Ψ γ z|≤2*C :=
    cavityGeneratedSingleOriginOriginalFreshExpectation_abs_le D μ a W c γ F C hC hbound i _
  have he γ : A=ᵐ[N.restrict (E γ)] Ψ γ := by
    filter_upwards [ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ),
      ae_restrict_of_ae (cavityGeneratedStreamingOriginValid_compProd_ae μ a W c M)] with z hz hv
    change (∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ=>F (z.1,Function.update σ c τ)) i z.2 ∂cavityGeneratedForestTerminalKernel D μ a W z.1)=_
    have hmasks σ : cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clockTemplate.clock z.1 c)
        (W.tree c) (fun τ=>F (z.1,Function.update σ c τ)) i z.2 =
        nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
          (fun τ=>F (z.1,Function.update σ c τ)) (.originalFresh i
            (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)) :=
      cavityGeneratedSelectedOriginPayload_eq_of_streaming_valid W c z.1 z.2 hv _
    rw [integral_congr_ae (.of_forall hmasks)]
    exact cavityGeneratedSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz
  have hp := chart_integrable_sum N E (measurableSet_cavityGeneratedSingleOriginChartEvent W c)
    (cavityGeneratedSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedSingleOriginChartEvent_cover_ae μ a W c M horder) A Ψ hm (2*C) hb he
  refine ⟨hp.1,?_⟩
  simp_rw [cavityGeneratedOriginalFreshChartMeasure_source_receiver D μ a W c M _ F hF i]
  rw [←Finset.mul_sum,←hp.2]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  exact integral_congr_ae ((he γ).trans ((ae_restrict_mem
    (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono
      fun z hz=>(cavityGeneratedSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz).symm)).symm

theorem cavityGeneratedStreamingCurrent_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedStreamingCurrentSourceValue D μ a W c F)
      (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ∧
    (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
        ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) =
    ∫z,cavityGeneratedStreamingCurrentSourceValue D μ a W c F z
      ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let N := M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c
  let A := cavityGeneratedStreamingCurrentSourceValue D μ a W c F
  let E := cavityGeneratedSingleOriginChartEvent W c
  let Ψ : PrintedGeneratedOriginChart (W.component c) →
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) → ℝ :=
    fun γ z=>Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)*
    cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F
      (Fin.snoc z.1 (cavityGeneratedOriginSelectionClock W c z))
  have hcdf : Measurable (fun z=>Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (measurable_cavityGeneratedOriginSelectionClock W c))
  have hm γ : Measurable (Ψ γ) := hcdf.mul
    ((measurable_cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F hF).comp
      (cavityGeneratedSingleOriginChart_append_measurable W c))
  have hb γ z : |Ψ γ z|≤2*C := by
    rw [abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg μ _)]
    exact (mul_le_mul (Paper.parisiCDF_le_one μ _)
      (cavityGeneratedSingleOriginCurrentExpectation_abs_le D μ a W c γ F C hC hbound _)
      (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  have he γ : A=ᵐ[N.restrict (E γ)] Ψ γ := by
    filter_upwards [ae_restrict_mem (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ),
      ae_restrict_of_ae (cavityGeneratedStreamingOriginValid_compProd_ae μ a W c M)] with z hz hv
    change (∫σ,cavityGeneratedSelectedCurrentPayload D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
      (fun τ=>F (z.1,Function.update σ c τ)) z.2 ∂cavityGeneratedForestTerminalKernel D μ a W z.1)=_
    have hmasks σ : cavityGeneratedSelectedCurrentPayload D μ a (W.clockTemplate.clock z.1 c)
        (W.tree c) (fun τ=>F (z.1,Function.update σ c τ)) z.2 =
        Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)*
          nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
            (fun τ=>F (z.1,Function.update σ c τ))
            (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)) :=
      cavityGeneratedSelectedOriginPayload_eq_of_streaming_valid W c z.1 z.2 hv _
    rw [integral_congr_ae (.of_forall hmasks),integral_const_mul]
    exact congrArg (fun t : ℝ=>Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)*t)
      (cavityGeneratedSingleOrigin_current_event_receiver D μ a W c γ F z hz)
  have hp := chart_integrable_sum N E (measurableSet_cavityGeneratedSingleOriginChartEvent W c)
    (cavityGeneratedSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedSingleOriginChartEvent_cover_ae μ a W c M horder) A Ψ hm (2*C) hb he
  refine ⟨hp.1,?_⟩
  simp_rw [cavityGeneratedCurrentChartMeasure_source_receiver D μ a W c M _ F hF]
  rw [←hp.2]
  apply Finset.sum_congr rfl
  intro γ _
  apply integral_congr_ae
  exact (he γ).trans ((ae_restrict_mem
    (measurableSet_cavityGeneratedSingleOriginChartEvent W c γ)).mono
      fun z hz=>congrArg (fun t : ℝ=>Paper.parisiCDF μ (cavityGeneratedOriginSelectionClock W c z)*t)
        (cavityGeneratedSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm) |>.symm

end QuantitativeFollowup
