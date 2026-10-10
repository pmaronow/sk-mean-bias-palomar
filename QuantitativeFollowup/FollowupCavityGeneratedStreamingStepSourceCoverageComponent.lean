module
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageDefinitions
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageFubini

@[expose] public section

/-! Exact component coverage under the actual retained history measure.
Every term is integrable by its genuine source receiver; neither a
partition identity nor an integrability conclusion is supplied by the
caller. The two selections in the cross term remain on the original
component. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {n m : ℕ}
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option maxHeartbeats 1900000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem cavityGeneratedStreamingComponent_source_coverage
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedStreamingComponentSelectedSource D μ a W c F) M ∧
    cavityGeneratedStreamingComponentSuccessorIntegralSum D μ a W c M F =
      ∫h,cavityGeneratedStreamingComponentSelectedSource D μ a W c F h ∂M := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let κ := cavityGeneratedOriginSelectionKernel μ a W c
  let ν := parisiFreeMeasure μ a
  let P := cavityGeneratedForestTerminalKernel D μ a W
  let test := fun h σ=>cavityGeneratedForestPartialTerminalTest W.depth W.tree
    (fun τ=>F (h,τ)) c σ
  have htest (h : CavityGeneratedHistory Paper.Overlap m)
      (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
      test h σ = (fun τ=>F (h,Function.update σ c τ)) := by
    funext τ
    exact cavityGeneratedForestPartialTerminalTest_fin_apply W.depth W.tree
      (fun τ=>F (h,τ)) c σ τ
  let old := fun h=>∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
    cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h
  let ofresh := fun i h=>∫g,∫σ,cavityGeneratedSelectedOriginalFreshPayload D μ a
    (W.clockTemplate.clock h c) (W.tree c) (test h σ) i g ∂P h ∂κ h
  let freshSum := fun h=>∑i : ObservationLeaf (W.tree c),ofresh i h
  let cross := fun h=>∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a
    (W.clockTemplate.clock h c) (W.tree c) (test h σ) g ∂P h ∂(κ h).prod (κ h)
  let current := fun h=>∫g,∫σ,cavityGeneratedSelectedCurrentPayload D μ a
    (W.clockTemplate.clock h c) (W.tree c) (test h σ) g ∂P h ∂κ h
  let future := fun h=>∫g,∫σ,cavityGeneratedSelectedFuturePayload D μ a
    (W.clockTemplate.clock h c) (W.tree c) (test h σ) g ∂P h ∂(κ h).prod ν
  let mean := fun h=>∫σ,F (h,σ) ∂P h
  let normalizer := fun h=>a*mean h*(∫l,nativeStreamingFreshDefectMoment D μ a l ∂ν)
  have iold i k : Integrable (cavityGeneratedStreamingOriginalExpectation D μ a W c i k F) M :=
    (integrable_const (2*C)).mono'
      (measurable_cavityGeneratedStreamingOriginalExpectation D μ a W c i k F hF).aestronglyMeasurable
      (.of_forall fun h=>by simpa only [Real.norm_eq_abs] using
        (abs_cavityGeneratedStreamingOriginalExpectation_le D μ a W c i k F C hC
          (fun h σ=>hbound (h,σ)) h))
  have io : Integrable old M := integrable_finset_sum _ (fun i _=>
    integrable_finset_sum _ (fun k _=>iold i k))
  have po i := cavityGeneratedStreamingOriginalFresh_source_partition
    D μ a ha hμ W c M horder F hF C hC hbound i
  have ifresh i : Integrable (ofresh i) M := by
    have hi := cavityGeneratedStreaming_integrable_compProd_fiber M κ
      (cavityGeneratedStreamingOriginalFreshSourceValue D μ a W c F i) (po i).1
    simpa only [ofresh,cavityGeneratedStreamingOriginalFreshSourceValue,←htest,κ,P] using hi
  have ifs : Integrable freshSum M := integrable_finset_sum _ (fun i _=>ifresh i)
  have px := cavityGeneratedCrossOrigin_source_forest_integral
    D μ a ha hμ W c M horder F hF C hC hbound
  have ix : Integrable cross M := px.1
  have pc := cavityGeneratedStreamingCurrent_source_partition
    D μ a ha hμ W c M horder F hF C hC hbound
  have ic : Integrable current M := by
    have hi := cavityGeneratedStreaming_integrable_compProd_fiber M κ
      (cavityGeneratedStreamingCurrentSourceValue D μ a W c F) pc.1
    simpa only [current,cavityGeneratedStreamingCurrentSourceValue,←htest,κ,P] using hi
  have pf := cavityGeneratedFutureOrigin_source_partition
    D μ a ha hμ W c M horder F hF C hC hbound
  have pfi := cavityGeneratedStreaming_integral_compProd_const_pair M κ ν
    (cavityGeneratedFutureOriginSourceValue D μ a W c F) pf.1
  have iy : Integrable future M := by
    simpa only [future,cavityGeneratedFutureOriginSourceValue,←htest,κ,P,ν] using pfi.1
  have hmean : Measurable mean := by
    simpa only [mean,P] using
      hF.stronglyMeasurable.integral_kernel_prod_right'
        (κ:=cavityGeneratedForestTerminalKernel D μ a W) |>.measurable
  have imean : Integrable mean M :=
    (integrable_const C).mono' hmean.aestronglyMeasurable (.of_forall fun h=>by
      simpa only [mean,P,Real.norm_eq_abs,probReal_univ,mul_one] using
        norm_integral_le_of_norm_le_const (μ:=P h) (f:=fun σ=>F (h,σ))
          (C:=C) (.of_forall fun σ=>by simpa only [Real.norm_eq_abs] using hbound (h,σ)))
  have iz : Integrable normalizer M := (imean.const_mul a).mul_const _
  have hs (h : CavityGeneratedHistory Paper.Overlap m) :
      cavityGeneratedStreamingComponentSelectedSource D μ a W c F h =
        old h + (-2*freshSum h) + cross h + current h + future h + normalizer h := by
    rfl
  have ih := ((((io.add (ifs.const_mul (-2))).add ix).add ic).add iy).add iz
  refine ⟨ih.congr (.of_forall fun h=>(hs h).symm),?_⟩
  have ho : (∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
      ∫h,cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h ∂M) =∫h,old h ∂M := by
    rw [show (fun h=>old h)=(fun h=>∑i : ObservationLeaf (W.tree c),∑k : ObservationLeaf (W.tree c),
      cavityGeneratedStreamingOriginalExpectation D μ a W c i k F h) from rfl]
    rw [integral_finset_sum _ (fun i _=>integrable_finset_sum _ (fun k _=>iold i k))]
    simp_rw [integral_finset_sum _ (fun k _=>iold _ k)]
  have hof i : (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginOriginalFreshExpectation D μ a W c γ F i H
        ∂cavityGeneratedOriginalFreshChartMeasure μ a W c M γ) =2*∫h,ofresh i h ∂M := by
    rw [(po i).2,Measure.integral_compProd (po i).1]
    simp only [ofresh,κ,P,cavityGeneratedStreamingOriginalFreshSourceValue,←htest]
  have hcurrent : (∑γ : PrintedGeneratedOriginChart (W.component c),
      ∫H,cavityGeneratedSingleOriginCurrentExpectation D μ a W c γ F H
        ∂cavityGeneratedCurrentChartMeasure μ a W c M γ) =∫h,current h ∂M := by
    rw [pc.2,Measure.integral_compProd pc.1]
    simp only [current,κ,P,cavityGeneratedStreamingCurrentSourceValue,←htest]
  have hfuture : (∑γ : PrintedGeneratedOriginChart (W.component c),∑j : Fin (W.depth c),
      ∫H,cavityGeneratedFutureOriginExpectation D μ a W c γ j F H
        ∂cavityGeneratedFutureOriginChartSourceMeasure μ a W c M γ j) =∫h,future h ∂M := by
    rw [pf.2,pfi.2]
    simp only [future,κ,P,ν,cavityGeneratedFutureOriginSourceValue,←htest]
  have hnormal : (∫H,printedGeneratedNormalizerSourceExpectation D μ a W (fun h σ=>F (h,σ)) H
      ∂cavityGeneratedNormalizerFamilyMeasure a ν M) =∫h,normalizer h ∂M := by
    simpa only [normalizer,mean,P,ν,cavityGeneratedForestTerminalKernel_apply,
      Function.uncurry_apply_pair] using printedGeneratedNormalizerFamily_source_receiver_independent
        D μ a ha.1 W M (fun h σ=>F (h,σ)) hF
  unfold cavityGeneratedStreamingComponentSuccessorIntegralSum
  rw [ho]
  simp_rw [hof]
  rw [px.2,hcurrent,hfuture,hnormal]
  rw [←Finset.mul_sum,←integral_finset_sum _ (fun i _=>ifresh i)]
  rw [integral_congr_ae (.of_forall hs)]
  change (∫h,old h ∂M)-2*(∫h,freshSum h ∂M)+(∫h,cross h ∂M)+
    (∫h,current h ∂M)+(∫h,future h ∂M)+(∫h,normalizer h ∂M)=_
  have hlin := integral_add' ((((io.add (ifs.const_mul (-2))).add ix).add ic).add iy) iz
  rw [integral_add' (((io.add (ifs.const_mul (-2))).add ix).add ic) iy,
    integral_add' ((io.add (ifs.const_mul (-2))).add ix) ic,
    integral_add' (io.add (ifs.const_mul (-2))) ix,
    integral_add' io (ifs.const_mul (-2))] at hlin
  simp only [Pi.add_apply] at hlin
  rw [hlin,integral_const_mul]
  ring

end QuantitativeFollowup
