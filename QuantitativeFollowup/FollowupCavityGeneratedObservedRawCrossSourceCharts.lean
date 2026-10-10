module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossSourcePointwise

@[expose] public section

/-! The genuine finite chart partition reconstructs the unrestricted
original double-selection source, with no chart-count multiplier. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m n : ℕ}

theorem cavityGeneratedObservedRawCrossChart_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (γ₁ γ₂ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ) (hF : Measurable F) :
    (∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ₁ γ₂ k F H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ₁ γ₂ k M) =
      ∫z,cavityGeneratedObservedRawCrossSourceValue D μ a W c F z
        ∂((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ⊗ₘ
          (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).comap Prod.fst measurable_fst).restrict
            (cavityGeneratedObservedRawCrossChartEvent W c γ₁ γ₂ k) := by
  rw [cavityGeneratedObservedRawCrossChartMeasure,cavityGeneratedRawOriginCrossSourceMeasure,integral_map
    (measurable_cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
    (measurable_cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ₁ γ₂ k F hF).aestronglyMeasurable]
  apply integral_congr_ae
  exact (ae_restrict_mem (measurableSet_cavityGeneratedObservedRawCrossChartEvent W c γ₁ γ₂ k)).mono
    (fun z hz=>(cavityGeneratedObservedRawCross_source_event_receiver D μ a W c γ₁ γ₂ k F z hz).symm)

theorem cavityGeneratedObservedRawCross_source_receiver
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedObservedRawCrossSourceValue D μ a W c F)
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ⊗ₘ
        (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).comap Prod.fst measurable_fst) ∧
    (∑γ₁,∑γ₂,∑k,
      ∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ₁ γ₂ k F H
        ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ₁ γ₂ k M) =
      ∫z,cavityGeneratedObservedRawCrossSourceValue D μ a W c F z
        ∂((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ⊗ₘ
          (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).comap Prod.fst measurable_fst) := by
  classical
  let N := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ⊗ₘ
    (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).comap Prod.fst measurable_fst
  let G := CavityGeneratedObservedRawOriginChart (W.tree c) ×
    (CavityGeneratedObservedRawOriginChart (W.tree c) × NativeStreamingGeneratedCrossEdgeChart)
  let E := fun s : G=>cavityGeneratedObservedRawCrossChartEvent W c s.1 s.2.1 s.2.2
  let f := cavityGeneratedObservedRawCrossSourceValue D μ a W c F
  have hE s : MeasurableSet (E s) := measurableSet_cavityGeneratedObservedRawCrossChartEvent W c _ _ _
  have hp : (∑s : G,N.restrict (E s))=N :=
    finiteMeasureChartPartition_sum_restrict N E hE
      (cavityGeneratedObservedRawCrossChartEvent_disjoint W c)
      (by
        filter_upwards [cavityGeneratedObservedRawCrossChartEvent_cover_ae μ a W c M horder] with z hz
        rcases hz with ⟨γ₁,γ₂,k,hk⟩
        exact ⟨(γ₁,γ₂,k),hk⟩)
  have his (s : G) : Integrable f (N.restrict (E s)) := by
    have hi : Integrable (fun z=>cavityGeneratedObservedRawCrossChartExpectation D μ a W c s.1 s.2.1 s.2.2 F
        (cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.tree c) z)) (N.restrict (E s)) :=
      (integrable_const (2*C)).mono'
        (((measurable_cavityGeneratedObservedRawCrossChartExpectation D μ a W c _ _ _ F hF).comp
          (measurable_cavityGeneratedRawOriginDoubleAppendedHistory (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c))).aestronglyMeasurable)
        (.of_forall fun z=>by simpa only [Real.norm_eq_abs] using
          abs_cavityGeneratedObservedRawCrossChartExpectation_le D μ a W c _ _ _ F C hC hbound _)
    exact hi.congr ((ae_restrict_mem (hE s)).mono fun z hz=>
      (cavityGeneratedObservedRawCross_source_event_receiver D μ a W c _ _ _ F z hz).symm)
  have hi : Integrable f N := by
    rw [←hp]
    exact integrable_finsetSum_measure.mpr (fun s _=>his s)
  refine ⟨hi,?_⟩
  have hsum : (∑s : G,∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c s.1 s.2.1 s.2.2 F H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c s.1 s.2.1 s.2.2 M) =∫z,f z ∂N := by
    calc
      _ =∑s : G,∫z,f z ∂N.restrict (E s) := by
        apply Finset.sum_congr rfl
        intro s _
        exact cavityGeneratedObservedRawCrossChart_source_receiver D μ a W c M _ _ _ F hF
      _ =∫z,f z ∂(∑s : G,N.restrict (E s)) :=
        (integral_finsetSum_measure (fun s _=>his s)).symm
      _ =_ := by rw [hp]
  simpa only [G,Fintype.sum_prod_type,N,f] using hsum


end QuantitativeFollowup
