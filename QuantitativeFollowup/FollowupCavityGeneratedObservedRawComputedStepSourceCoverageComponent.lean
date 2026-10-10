module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageDefinitions
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageSupport
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageSingle
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageFuture
public import QuantitativeFollowup.FollowupCavityGeneratedStreamingStepSourceCoverageFubini

@[expose] public section

/-! Each actual raw component source is received by its six computed
successor families. The source receivers derive integrability; neither
an output-law identity nor a source equality is supplied by the caller. -/
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

theorem cavityGeneratedObservedRawStreamingComponent_source_coverage
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M, h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z, |F z|≤L) :
    Integrable (cavityGeneratedObservedRawStreamingComponentSelectedSource D μ a W c F) M ∧
    cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum D μ a W c M F =
      ∫h, cavityGeneratedObservedRawStreamingComponentSelectedSource D μ a W c F h ∂M := by
  let κ := cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)
  let ν := parisiFreeMeasure μ a
  let P := cavityGeneratedRawForestTerminalKernel D μ a W.depth W.tree W.clock
    W.measurable_clock W.clock_antitone
  let test := fun h σ => cavityGeneratedForestPartialTerminalTest W.depth W.tree
    (fun τ => F (h,τ)) c σ
  have htest (h : CavityGeneratedHistory Paper.Overlap m)
      (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
      test h σ = (fun τ => F (h,Function.update σ c τ)) := by
    funext τ
    exact cavityGeneratedForestPartialTerminalTest_fin_apply W.depth W.tree
      (fun τ => F (h,τ)) c σ τ
  let old := fun h => ∑i : ObservationLeaf (W.tree c), ∑k : ObservationLeaf (W.tree c),
    cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h
  let ofresh := fun i h => ∫g, ∫σ, cavityGeneratedSelectedOriginalFreshPayload D μ a
    (W.clock h c) (W.tree c) (test h σ) i g ∂P h ∂κ h
  let freshSum := fun h => ∑i : ObservationLeaf (W.tree c), ofresh i h
  let cross := fun h => ∫g, ∫σ, cavityGeneratedSelectedCrossPayload D μ a
    (W.clock h c) (W.tree c) (test h σ) g ∂P h ∂(κ h).prod (κ h)
  let current := fun h => ∫g, ∫σ, cavityGeneratedSelectedCurrentPayload D μ a
    (W.clock h c) (W.tree c) (test h σ) g ∂P h ∂κ h
  let future := fun h => ∫g, ∫σ, cavityGeneratedSelectedFuturePayload D μ a
    (W.clock h c) (W.tree c) (test h σ) g ∂P h ∂(κ h).prod ν
  let mean := cavityGeneratedObservedRawStreamingBaseExpectation D μ a W F
  let normalizer := fun h => a * mean h * (∫l, nativeStreamingFreshDefectMoment D μ a l ∂ν)
  have iold i k : Integrable (cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F) M :=
    integrable_cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k M F hF L hL hbound
  have io : Integrable old M := integrable_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun k _ => iold i k))
  have po i := cavityGeneratedObservedRawStreamingOriginalFresh_source_partition
    D μ a ha hμ W c M hsupport F hF L hL hbound i
  have ifresh i : Integrable (ofresh i) M := by
    have hi := cavityGeneratedStreaming_integrable_compProd_fiber M κ
      (cavityGeneratedObservedRawStreamingOriginalFreshSourceValue D μ a W c F i) (po i).1
    simpa only [ofresh,cavityGeneratedObservedRawStreamingOriginalFreshSourceValue,←htest,κ,P,
      cavityGeneratedRawForestTerminalKernel_apply] using hi
  have ifs : Integrable freshSum M := integrable_finset_sum _ (fun i _ => ifresh i)
  have px := cavityGeneratedObservedRawCross_source_forest_integral
    D μ a ha hμ W c M hsupport F hF L hL hbound
  have ix : Integrable cross M := by
    simpa only [cross,←htest,κ,P,cavityGeneratedRawForestTerminalKernel_apply] using px.1
  have pc := cavityGeneratedObservedRawStreamingCurrent_source_partition
    D μ a ha hμ W c M hsupport F hF L hL hbound
  have ic : Integrable current M := by
    have hi := cavityGeneratedStreaming_integrable_compProd_fiber M κ
      (cavityGeneratedObservedRawStreamingCurrentSourceValue D μ a W c F) pc.1
    simpa only [current,cavityGeneratedObservedRawStreamingCurrentSourceValue,←htest,κ,P,
      cavityGeneratedRawForestTerminalKernel_apply] using hi
  have pf := cavityGeneratedObservedRawStreamingFuture_source_partition
    D μ a W c M hsupport F hF L hL hbound
  have hfi : Integrable (cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F)
      ((M ⊗ₘ κ) ⊗ₘ Kernel.const
        (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ν) := by
    simpa only [Measure.compProd_const,κ,ν] using pf.1
  have pfi := cavityGeneratedStreaming_integral_compProd_const_pair M κ ν
    (cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F) hfi
  have iy : Integrable future M := by
    simpa only [future,cavityGeneratedObservedRawStreamingFutureSourceValue,←htest,κ,P,ν,
      cavityGeneratedRawForestTerminalKernel_apply] using pfi.1
  have iz : Integrable normalizer M :=
    integrable_cavityGeneratedObservedRawStreamingNormalizerSource D μ a W M F hF L hbound
  have hs (h : CavityGeneratedHistory Paper.Overlap m) :
      cavityGeneratedObservedRawStreamingComponentSelectedSource D μ a W c F h =
        old h + (-2*freshSum h) + cross h + current h + future h + normalizer h := by
    rfl
  have ih := ((((io.add (ifs.const_mul (-2))).add ix).add ic).add iy).add iz
  refine ⟨ih.congr (.of_forall fun h => (hs h).symm), ?_⟩
  have ho : (∑i : ObservationLeaf (W.tree c), ∑k : ObservationLeaf (W.tree c),
      ∫h, cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h ∂M) =
      ∫h, old h ∂M := by
    rw [show (fun h => old h) = (fun h => ∑i : ObservationLeaf (W.tree c), ∑k : ObservationLeaf (W.tree c),
      cavityGeneratedObservedRawStreamingOriginalExpectation D μ a W c i k F h) from rfl]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ => iold i k))]
    simp_rw [integral_finset_sum _ (fun k _ => iold _ k)]
  have hof i : (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H, cavityGeneratedObservedRawSingleOriginOriginalFreshExpectation D μ a W c γ F i H
        ∂cavityGeneratedObservedRawOriginalFreshChartMeasure μ a W c M γ) =
      2 * ∫h, ofresh i h ∂M := by
    rw [(po i).2,Measure.integral_compProd (po i).1]
    simp only [ofresh,κ,P,cavityGeneratedObservedRawStreamingOriginalFreshSourceValue,←htest,
      cavityGeneratedRawForestTerminalKernel_apply]
  have hcurrent : (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c),
      ∫H, cavityGeneratedObservedRawSingleOriginCurrentExpectation D μ a W c γ F H
        ∂cavityGeneratedObservedRawCurrentChartMeasure μ a W c M γ) =
      ∫h, current h ∂M := by
    rw [pc.2,Measure.integral_compProd pc.1]
    simp only [current,κ,P,cavityGeneratedObservedRawStreamingCurrentSourceValue,←htest,
      cavityGeneratedRawForestTerminalKernel_apply]
  have hfuture : (∑γ : CavityGeneratedObservedRawOriginChart (W.tree c), ∑j : Fin (W.depth c),
      ∫H, cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H
        ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
      ∫h, future h ∂M := by
    rw [pf.2]
    simpa only [Measure.compProd_const,future,cavityGeneratedObservedRawStreamingFutureSourceValue,
      ←htest,κ,P,ν,cavityGeneratedRawForestTerminalKernel_apply] using pfi.2
  have hnormal : (∫H, cavityGeneratedObservedRawNormalizerSourceExpectation D μ a W (fun h σ => F (h,σ)) H
      ∂cavityGeneratedNormalizerFamilyMeasure a ν M) = ∫h, normalizer h ∂M := by
    simpa only [normalizer,mean,ν,cavityGeneratedObservedRawStreamingBaseExpectation,
      Function.uncurry_apply_pair] using cavityGeneratedObservedRawNormalizerFamily_source_receiver_independent
        D μ a ha.1 W M (fun h σ => F (h,σ)) hF
  unfold cavityGeneratedObservedRawStreamingComponentSuccessorIntegralSum
  rw [ho]
  simp_rw [hof]
  rw [px.2,hcurrent,hfuture,hnormal]
  rw [←Finset.mul_sum,←integral_finset_sum _ (fun i _ => ifresh i)]
  rw [integral_congr_ae (.of_forall hs)]
  change (∫h, old h ∂M) - 2*(∫h, freshSum h ∂M) + (∫h, cross h ∂M) +
    (∫h, current h ∂M) + (∫h, future h ∂M) + (∫h, normalizer h ∂M) = _
  have hlin := integral_add' ((((io.add (ifs.const_mul (-2))).add ix).add ic).add iy) iz
  rw [integral_add' (((io.add (ifs.const_mul (-2))).add ix).add ic) iy,
    integral_add' ((io.add (ifs.const_mul (-2))).add ix) ic,
    integral_add' (io.add (ifs.const_mul (-2))) ix,
    integral_add' io (ifs.const_mul (-2))] at hlin
  simp only [Pi.add_apply] at hlin
  rw [hlin,integral_const_mul]
  ring

end QuantitativeFollowup
