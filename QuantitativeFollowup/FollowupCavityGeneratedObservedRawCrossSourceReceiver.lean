module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawCrossSourceCharts
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawStreamingStepSourceCoverageStatic
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginCellSupport
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! Actual halfclosed cell support removes both source masks. Genuine
product association then exposes the original-selection-first forest
source integral, with physical endpoint atoms and no chart multiplier. -/
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

def cavityGeneratedObservedRawCrossSelectedSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      (CavityGeneratedOriginSelection (W.tree c)×CavityGeneratedOriginSelection (W.tree c))) : ℝ :=
  ∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clock z.1 c) (W.tree c)
    (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (z.1,τ)) c σ) z.2
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1) : Measure _)

private theorem rawCrossPartialTest_eq
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ=
      (fun τ=>F (h,Function.update σ c τ)) := by
  funext τ
  exact cavityGeneratedForestPartialTerminalTest_fin_apply W.depth W.tree (fun τ=>F (h,τ)) c σ τ

theorem cavityGeneratedObservedRawCross_source_selected_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedObservedRawCrossSelectedSourceValue D μ a W c F)
      (M ⊗ₘ ((cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)) ×ₖ
        (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)))) ∧
    (∑γ,∑δ,∑k,∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ k M)=
      ∫h,∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) : Measure _)
        ∂(cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h).prod
          (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h) ∂M := by
  classical
  let κ := cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)
  let N := (M ⊗ₘ κ) ⊗ₘ κ.comap Prod.fst measurable_fst
  let e : CavityGeneratedObservedRawCrossPayload W c ≃ᵐ
      CavityGeneratedHistory Paper.Overlap m ×
        (CavityGeneratedOriginSelection (W.tree c)×CavityGeneratedOriginSelection (W.tree c)) := MeasurableEquiv.prodAssoc
  let f := cavityGeneratedObservedRawCrossSelectedSourceValue D μ a W c F
  have hk : κ ⊗ₖ κ.comap Prod.fst measurable_fst=κ ×ₖ κ := by
    ext h s hs : 2
    rw [Kernel.compProd_apply hs,Kernel.prod_apply,Measure.prod_apply hs]
    simp only [Kernel.comap_apply]
  have hp : N.map e=M ⊗ₘ (κ ×ₖ κ) := by
    change ((M ⊗ₘ κ) ⊗ₘ κ.comap Prod.fst measurable_fst).map MeasurableEquiv.prodAssoc=_
    rw [Measure.compProd_assoc',hk]
  obtain ⟨hi,hsource⟩ := cavityGeneratedObservedRawCross_source_receiver D μ a ha hμ W c M hsupport F hF C hC hbound
  have he : (fun z=>f (e z)) =ᵐ[N] cavityGeneratedObservedRawCrossSourceValue D μ a W c F := by
    filter_upwards [cavityGeneratedRawOriginDoubleSelection_ae_cell_valid μ a
      (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) M] with z hz
    unfold f cavityGeneratedObservedRawCrossSelectedSourceValue cavityGeneratedObservedRawCrossSourceValue
    apply integral_congr_ae
    refine .of_forall fun σ=>?_
    change cavityGeneratedSelectedCrossPayload D μ a (W.clock z.1.1 c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (z.1.1,τ)) c σ) (z.1.2,z.2)=
      nativeStreamingPatternMoment D μ a (W.clock z.1.1 c) (W.tree c)
        (fun τ=>F (z.1.1,Function.update σ c τ))
        (.cross (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)
          (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
    unfold cavityGeneratedSelectedCrossPayload cavityGeneratedSelectedOriginPayload
    rw [cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.1,
      cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.2,rawCrossPartialTest_eq W c F z.1.1 σ]
  have hif : Integrable f (M ⊗ₘ (κ ×ₖ κ)) := by
    rw [←hp]
    exact (integrable_map_equiv e f).mpr (hi.congr he.symm)
  refine ⟨hif,?_⟩
  calc
    _ =∫z,cavityGeneratedObservedRawCrossSourceValue D μ a W c F z ∂N := hsource
    _ =∫z,f (e z) ∂N := integral_congr_ae he.symm
    _ =∫z,f z ∂N.map e :=
      (integral_map e.measurable.aemeasurable (by rw [hp]; exact hif.aestronglyMeasurable)).symm
    _ =∫z,f z ∂(M ⊗ₘ (κ ×ₖ κ)) := by rw [hp]
    _ =∫h,∫g,f (h,g) ∂(κ ×ₖ κ) h ∂M := Measure.integral_compProd hif
    _ =_ := by simp only [κ,Kernel.prod_apply,f,cavityGeneratedObservedRawCrossSelectedSourceValue]

theorem cavityGeneratedObservedRawCross_source_forest_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (fun h=>∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
      ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) : Measure _)
      ∂(cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h).prod
        (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h)) M ∧
    (∑γ,∑δ,∑k,∫H,cavityGeneratedObservedRawCrossChartExpectation D μ a W c γ δ k F H
      ∂cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ k M)=
      ∫h,∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock h) : Measure _)
        ∂(cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h).prod
          (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) h) ∂M := by
  obtain ⟨hi,heq⟩ := cavityGeneratedObservedRawCross_source_selected_integral D μ a ha hμ W c M hsupport F hF C hC hbound
  refine ⟨?_,heq⟩
  simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply,Kernel.prod_apply,
    cavityGeneratedObservedRawCrossSelectedSourceValue] using hi.integral_compProd

end QuantitativeFollowup
