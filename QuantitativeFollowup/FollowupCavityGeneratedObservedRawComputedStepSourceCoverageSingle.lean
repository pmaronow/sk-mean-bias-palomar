module
public import QuantitativeFollowup.SupportingGeneratedRawSingleOriginSourceReceiver
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSingleChartCoverage
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverageStatic

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

private theorem selectedOriginPayload_eq_of_valid {J : ℕ}
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (g : CavityGeneratedOriginSelection T)
    (hg : cavityGeneratedOriginCellValid q T (cavityGeneratedOriginSelectionOrigin T g))
    (Φ : NativeStreamingOrigin T → ℝ) :
    cavityGeneratedSelectedOriginPayload q T Φ g =
      Φ (cavityGeneratedOriginSelectionOrigin T g) := by
  rcases g with i | (i | u)
  · rfl
  · exact if_pos hg
  · rfl

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

def cavityGeneratedObservedRawStreamingOriginalFreshSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (i : ObservationLeaf (W.tree c))
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) : ℝ :=
  ∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clock z.1 c) (W.tree c)
    (fun τ=>F (z.1,Function.update σ c τ)) i z.2 ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1) : Measure _)

def cavityGeneratedObservedRawStreamingCurrentSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) : ℝ :=
  ∫σ,cavityGeneratedSelectedCurrentPayload D μ a (W.clock z.1 c) (W.tree c)
    (fun τ=>F (z.1,Function.update σ c τ)) z.2 ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1) : Measure _)

theorem cavityGeneratedObservedRawStreamingOriginalFresh_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C)
    (i : ObservationLeaf (W.tree c)) :
    Integrable (cavityGeneratedObservedRawStreamingOriginalFreshSourceValue D μ a W c F i)
      (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ∧
    (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H,cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i H
        ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) =
    2*∫z,cavityGeneratedObservedRawStreamingOriginalFreshSourceValue D μ a W c F i z
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) := by
  let N := M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)
  let A := cavityGeneratedObservedRawStreamingOriginalFreshSourceValue D μ a W c F i
  let E := cavityGeneratedObservedRawSingleOriginChartEvent W c
  let Ψ : CavityGeneratedObservedRawOriginChart (W.tree c) →
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) → ℝ :=
    fun γ z=>cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i
    (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z))
  have hm γ : Measurable (Ψ γ) :=
    (measurable_cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F hF i).comp
      (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c))
  have hb γ z : |Ψ γ z|≤2*C :=
    cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation_abs_le D μ a W c γ F C hC hbound i _
  have he γ : A=ᵐ[N.restrict (E γ)] Ψ γ := by
    filter_upwards [ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ),
      ae_restrict_of_ae (cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) M)] with z hz hv
    change (∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clock z.1 c) (W.tree c)
      (fun τ=>F (z.1,Function.update σ c τ)) i z.2 ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1) : Measure _))=_
    have hmasks σ : cavityGeneratedSelectedOriginalFreshPayload D μ a (W.clock z.1 c)
        (W.tree c) (fun τ=>F (z.1,Function.update σ c τ)) i z.2 =
        nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
          (fun τ=>F (z.1,Function.update σ c τ)) (.originalFresh i
            (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)) :=
      selectedOriginPayload_eq_of_valid (W.clock z.1 c) (W.tree c) z.2 hv _
    rw [integral_congr_ae (.of_forall hmasks)]
    exact cavityGeneratedObservedRawSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz
  have hp := chart_integrable_sum N E (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_cover_ae μ a W c M hsupport) A Ψ hm (2*C) hb he
  refine ⟨hp.1,?_⟩
  simp_rw [cavityGeneratedObservedRawOriginalFreshChartMeasure_source_receiver D μ a W c M _ F hF i]
  rw [←Finset.mul_sum,←hp.2]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  exact integral_congr_ae ((he γ).trans ((ae_restrict_mem
    (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono
      fun z hz=>(cavityGeneratedObservedRawSingleOrigin_originalFresh_event_receiver D μ a W c γ F i z hz).symm)).symm

theorem cavityGeneratedObservedRawStreamingCurrent_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedObservedRawStreamingCurrentSourceValue D μ a W c F)
      (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ∧
    (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H,cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
        ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) =
    ∫z,cavityGeneratedObservedRawStreamingCurrentSourceValue D μ a W c F z
      ∂(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) := by
  let N := M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)
  let A := cavityGeneratedObservedRawStreamingCurrentSourceValue D μ a W c F
  let E := cavityGeneratedObservedRawSingleOriginChartEvent W c
  let Ψ : CavityGeneratedObservedRawOriginChart (W.tree c) →
      (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) → ℝ :=
    fun γ z=>Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)*
    cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F
      (Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z))
  have hcdf : Measurable (fun z=>Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)) :=
    (Paper.parisiCDF_measurable μ).comp
      (measurable_subtype_coe.comp (measurable_cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)))
  have hm γ : Measurable (Ψ γ) := hcdf.mul
    ((measurable_cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F hF).comp
      (measurable_cavityGeneratedRawOriginAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)))
  have hb γ z : |Ψ γ z|≤2*C := by
    rw [abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg μ _)]
    exact (mul_le_mul (Paper.parisiCDF_le_one μ _)
      (cavityGeneratedObservedRawSingleOriginCurrentExpectation_abs_le D μ a W c γ F C hC hbound _)
      (abs_nonneg _) (by positivity)).trans_eq (one_mul _)
  have he γ : A=ᵐ[N.restrict (E γ)] Ψ γ := by
    filter_upwards [ae_restrict_mem (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ),
      ae_restrict_of_ae (cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) M)] with z hz hv
    change (∫σ,cavityGeneratedSelectedCurrentPayload D μ a (W.clock z.1 c) (W.tree c)
      (fun τ=>F (z.1,Function.update σ c τ)) z.2 ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1) : Measure _))=_
    have hmasks σ : cavityGeneratedSelectedCurrentPayload D μ a (W.clock z.1 c)
        (W.tree c) (fun τ=>F (z.1,Function.update σ c τ)) z.2 =
        Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)*
          nativeStreamingPatternMoment D μ a (W.clock z.1 c) (W.tree c)
            (fun τ=>F (z.1,Function.update σ c τ))
            (.current (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)) :=
      selectedOriginPayload_eq_of_valid (W.clock z.1 c) (W.tree c) z.2 hv _
    rw [integral_congr_ae (.of_forall hmasks),integral_const_mul]
    exact congrArg (fun t : ℝ=>Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)*t)
      (cavityGeneratedObservedRawSingleOrigin_current_event_receiver D μ a W c γ F z hz)
  have hp := chart_integrable_sum N E (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedObservedRawSingleOriginChartEvent_cover_ae μ a W c M hsupport) A Ψ hm (2*C) hb he
  refine ⟨hp.1,?_⟩
  simp_rw [cavityGeneratedObservedRawCurrentChartMeasure_source_receiver D μ a W c M _ F hF]
  rw [←hp.2]
  apply Finset.sum_congr rfl
  intro γ _
  apply integral_congr_ae
  exact (he γ).trans ((ae_restrict_mem
    (measurableSet_cavityGeneratedObservedRawSingleOriginChartEvent W c γ)).mono
      fun z hz=>congrArg (fun t : ℝ=>Paper.parisiCDF μ (cavityGeneratedRawOriginSelectionClock (fun h=>W.clock h c) (W.tree c) z)*t)
        (cavityGeneratedObservedRawSingleOrigin_current_event_receiver D μ a W c γ F z hz).symm) |>.symm

end QuantitativeFollowup
