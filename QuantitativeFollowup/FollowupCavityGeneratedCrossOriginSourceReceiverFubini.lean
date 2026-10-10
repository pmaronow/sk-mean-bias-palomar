module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginSourceReceiverSource
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionCellSupport
public import QuantitativeFollowup.FollowupCavityGeneratedForestStreamingReplacementBasis
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixMeasure
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayloadMeasurable
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd

@[expose] public section

/-! The finite chart sum is the literal original-history source integral.
Cell masks disappear only on their genuine halfclosed selection support,
and Fubini uses actual bounded measurable selected payloads. -/
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

def cavityGeneratedCrossOriginSelectedSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : CavityGeneratedHistory Paper.Overlap m ×
      (CavityGeneratedOriginSelection (W.tree c)×CavityGeneratedOriginSelection (W.tree c))) : ℝ :=
  ∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock z.1 c) (W.tree c)
    (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (z.1,τ)) c σ) z.2
    ∂cavityGeneratedForestTerminalKernel D μ a W z.1

private theorem crossSelectedPayload_abs_le {J : ℕ}
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ→Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T→ℝ) (C : ℝ) (hC : 0≤C)
    (hF : ∀σ,|F σ|≤C)
    (z : CavityGeneratedOriginSelection T×CavityGeneratedOriginSelection T) :
    |cavityGeneratedSelectedCrossPayload D μ a q T F z|≤2*C := by
  unfold cavityGeneratedSelectedCrossPayload cavityGeneratedSelectedOriginPayload
  apply abs_cavityGeneratedOriginCellMask_le q T _ (2*C) (by positivity)
  intro o
  apply abs_cavityGeneratedOriginCellMask_le q T _ (2*C) (by positivity)
  intro p
  exact abs_nativeStreamingPatternMoment_le D μ a q T F C hC hF _

private theorem crossPartialTest_eq
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree) :
    cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ =
      (fun τ=>F (h,Function.update σ c τ)) := by
  funext τ
  unfold cavityGeneratedForestPartialTerminalTest
  apply congrArg (fun η=>F (h,η))
  funext d
  by_cases hd : d=c
  · subst d
    simp only [Function.update_self]
  · simp [Function.update,hd]

private theorem crossSourceSection_swap
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (C : ℝ) (hC : 0≤C) (hF : ∀z,|F z|≤C)
    (h : CavityGeneratedHistory Paper.Overlap m) :
    (∫g, cavityGeneratedCrossOriginSelectedSourceValue D μ a W c F (h,g)
      ∂(cavityGeneratedOriginSelectionKernel μ a W c h).prod (cavityGeneratedOriginSelectionKernel μ a W c h)) =
      ∫σ,∫g,cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
        ∂(cavityGeneratedOriginSelectionKernel μ a W c h).prod (cavityGeneratedOriginSelectionKernel μ a W c h)
        ∂cavityGeneratedForestTerminalKernel D μ a W h := by
  haveI : IsFiniteMeasure (cavityGeneratedOriginSelectionKernel μ a W c h) :=
    cavityGeneratedOriginSelectionMeasure_finite μ a (W.clockTemplate.clock h c) (W.tree c) a
  let f := fun (σ : CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree)
      (g : CavityGeneratedOriginSelection (W.tree c)×CavityGeneratedOriginSelection (W.tree c)) =>
    cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
  have hm : Measurable (Function.uncurry f) := by
    apply measurable_from_prod_countable_right
    intro σ
    change Measurable (cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ))
    exact measurable_cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c)
      (antitone_nat_of_succ_le (W.clockTemplate.clock_step_le h c)) (W.tree c) _
  have hi : Integrable (Function.uncurry f)
      ((cavityGeneratedForestTerminalKernel D μ a W h).prod
        ((cavityGeneratedOriginSelectionKernel μ a W c h).prod
          (cavityGeneratedOriginSelectionKernel μ a W c h))) :=
    (integrable_const (2*C)).mono' hm.aestronglyMeasurable (.of_forall fun z=>by
      change |cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c z.1) z.2|≤2*C
      exact crossSelectedPayload_abs_le D μ a (W.clockTemplate.clock h c) (W.tree c) _ C hC
        (abs_cavityGeneratedForestPartialTerminalTest_le W.depth W.tree
          (fun τ=>F (h,τ)) C (fun τ=>hF (h,τ)) c z.1) z.2)
  exact (integral_integral_swap hi).symm

theorem cavityGeneratedCrossOrigin_source_selected_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (cavityGeneratedCrossOriginSelectedSourceValue D μ a W c F)
      (M ⊗ₘ (cavityGeneratedOriginSelectionKernel μ a W c ×ₖ cavityGeneratedOriginSelectionKernel μ a W c)) ∧
    (∑γ₁,∑γ₂,∑k,
      ∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F H
        ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k) =
      ∫h,∫σ,∫g,cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
        ∂(cavityGeneratedOriginSelectionKernel μ a W c h).prod (cavityGeneratedOriginSelectionKernel μ a W c h)
        ∂cavityGeneratedForestTerminalKernel D μ a W h ∂M := by
  classical
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let κ := cavityGeneratedOriginSelectionKernel μ a W c
  let N := (M ⊗ₘ κ) ⊗ₘ κ.comap Prod.fst measurable_fst
  let e : CavityGeneratedCrossOriginPayload W c ≃ᵐ
      CavityGeneratedHistory Paper.Overlap m ×
        (CavityGeneratedOriginSelection (W.tree c)×CavityGeneratedOriginSelection (W.tree c)) :=
    MeasurableEquiv.prodAssoc
  let f := cavityGeneratedCrossOriginSelectedSourceValue D μ a W c F
  have hk : κ ⊗ₖ κ.comap Prod.fst measurable_fst = κ ×ₖ κ := by
    ext h s hs : 2
    rw [Kernel.compProd_apply hs,Kernel.prod_apply,Measure.prod_apply hs]
    simp only [Kernel.comap_apply]
  have hp : N.map e = M ⊗ₘ (κ ×ₖ κ) := by
    change ((M ⊗ₘ κ) ⊗ₘ κ.comap Prod.fst measurable_fst).map
      MeasurableEquiv.prodAssoc = _
    rw [Measure.compProd_assoc',hk]
  obtain ⟨hi,hsource⟩ := cavityGeneratedCrossOrigin_source_receiver D μ a ha hμ W c M horder F hF C hC hbound
  have he : (fun z=>f (e z)) =ᵐ[N] cavityGeneratedCrossOriginSourceValue D μ a W c F := by
    filter_upwards [cavityGeneratedDoubleOriginSelection_ae_cell_valid μ a W c M] with z hz
    unfold f cavityGeneratedCrossOriginSelectedSourceValue cavityGeneratedCrossOriginSourceValue
    apply integral_congr_ae
    refine .of_forall fun σ=>?_
    change cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (z.1.1,τ)) c σ)
        (z.1.2,z.2) = nativeStreamingPatternMoment D μ a (W.clockTemplate.clock z.1.1 c) (W.tree c)
          (fun τ=>F (z.1.1,Function.update σ c τ))
          (.cross (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)
            (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2))
    unfold cavityGeneratedSelectedCrossPayload cavityGeneratedSelectedOriginPayload
    rw [cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.1,
      cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.2,
      crossPartialTest_eq W c F z.1.1 σ]
  have hif : Integrable f (M ⊗ₘ (κ ×ₖ κ)) := by
    rw [←hp]
    exact (integrable_map_equiv e f).mpr (hi.congr he.symm)
  refine ⟨hif,?_⟩
  calc
    _ =∫z,cavityGeneratedCrossOriginSourceValue D μ a W c F z ∂N := hsource
    _ =∫z,f (e z) ∂N := integral_congr_ae he.symm
    _ =∫z,f z ∂N.map e :=
      (integral_map e.measurable.aemeasurable (by rw [hp]; exact hif.aestronglyMeasurable)).symm
    _ =∫z,f z ∂(M ⊗ₘ (κ ×ₖ κ)) := by rw [hp]
    _ =∫h,∫g,f (h,g) ∂(κ ×ₖ κ) h ∂M := Measure.integral_compProd hif
    _ =_ := by
      apply integral_congr_ae
      refine .of_forall fun h=>?_
      simpa only [κ,Kernel.prod_apply] using crossSourceSection_swap D μ a W c F C hC hbound h

theorem cavityGeneratedCrossOrigin_source_forest_integral
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (C : ℝ) (hC : 0≤C) (hbound : ∀z,|F z|≤C) :
    Integrable (fun h=>∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a
      (W.clockTemplate.clock h c) (W.tree c)
      (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
      ∂cavityGeneratedForestTerminalKernel D μ a W h
      ∂(cavityGeneratedOriginSelectionKernel μ a W c h).prod
        (cavityGeneratedOriginSelectionKernel μ a W c h)) M ∧
    (∑γ₁,∑γ₂,∑k,
      ∫H,cavityGeneratedCrossOriginExpectation D μ a W c γ₁ γ₂ k F H
        ∂cavityGeneratedCrossOriginChartMeasure μ a W c M γ₁ γ₂ k) =
      ∫h,∫g,∫σ,cavityGeneratedSelectedCrossPayload D μ a (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedForestPartialTerminalTest W.depth W.tree (fun τ=>F (h,τ)) c σ) g
        ∂cavityGeneratedForestTerminalKernel D μ a W h
        ∂(cavityGeneratedOriginSelectionKernel μ a W c h).prod
          (cavityGeneratedOriginSelectionKernel μ a W c h) ∂M := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  obtain ⟨hi,heq⟩ := cavityGeneratedCrossOrigin_source_selected_integral
    D μ a ha hμ W c M horder F hF C hC hbound
  refine ⟨?_,heq.trans ?_⟩
  · simpa only [Kernel.const_apply,Kernel.prodMkLeft_apply,Kernel.prod_apply,
      cavityGeneratedCrossOriginSelectedSourceValue] using hi.integral_compProd
  · apply integral_congr_ae
    exact .of_forall fun h=>(crossSourceSection_swap D μ a W c F C hC hbound h).symm

end QuantitativeFollowup
