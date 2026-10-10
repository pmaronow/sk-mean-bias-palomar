module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawComputedStepSourceCoverageFutureExpectation
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawFutureChartCoverage
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload

@[expose] public section

/-! Actual raw future successor expectations reconstruct the selected
future payload on the original history and original selection. All old
terminal coordinates remain in the joint observable. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped BigOperators ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n m : ℕ}

private theorem selectedFutureCell_of_valid {J : ℕ}
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (F : TerminalSpins (Configuration (n+1)) T → ℝ) (j : ℕ)
    (g : CavityGeneratedOriginSelection T) (l : Paper.Overlap)
    (hg : cavityGeneratedOriginCellValid q T (cavityGeneratedOriginSelectionOrigin T g)) :
    cavityGeneratedSelectedFutureCellPayload D μ a q T F j (g,l) =
      if l∈Ioc (q (j+1)) (q j) ∧
          nativeStreamingOriginLevel q (cavityGeneratedOriginSelectionOrigin T g)<l
      then nativeStreamingPatternMoment D μ a q T F
        (.future (cavityGeneratedOriginSelectionOrigin T g) j l) else 0 := by
  rcases g with i | (z | u)
  · rfl
  · exact if_pos hg
  · rfl

def cavityGeneratedObservedRawStreamingFutureCellSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (j : Fin (W.depth c))
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) : ℝ :=
  ∫σ, cavityGeneratedSelectedFutureCellPayload D μ a (W.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ)) j (z.1.2,z.2)
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1.1) : Measure _)

def cavityGeneratedObservedRawStreamingFutureSourceValue
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (z : (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
      Paper.Overlap) : ℝ :=
  ∫σ, cavityGeneratedSelectedFuturePayload D μ a (W.clock z.1.1 c) (W.tree c)
    (fun τ=>F (z.1.1,Function.update σ c τ)) (z.1.2,z.2)
    ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1.1) : Measure _)

theorem cavityGeneratedObservedRawStreamingFutureCell_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L)
    (j : Fin (W.depth c)) :
    Integrable (cavityGeneratedObservedRawStreamingFutureCellSourceValue D μ a W c F j)
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)) ∧
    (∑γ,∫H,cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
    ∫z,cavityGeneratedObservedRawStreamingFutureCellSourceValue D μ a W c F j z
      ∂((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)) := by
  classical
  let P := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
    (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)
  let A := cavityGeneratedObservedRawStreamingFutureCellSourceValue D μ a W c F j
  let E := fun γ=>cavityGeneratedObservedRawFutureSourceEvent W c γ j
  let Ψ := fun γ z=>cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F
    (cavityGeneratedObservedRawFutureAppend W c z)
  have hm γ : Measurable (Ψ γ) :=
    (measurable_cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F hF).comp
      (measurable_cavityGeneratedObservedRawFutureAppend W c)
  have hi γ : Integrable ((E γ).indicator (Ψ γ)) P := by
    apply (integrable_const (2*L)).mono'
      ((hm γ).piecewise (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c γ j)
        measurable_const).aestronglyMeasurable
    refine .of_forall fun z=>?_
    change ‖(E γ).indicator (Ψ γ) z‖≤2*L
    by_cases hz : z∈E γ
    · rw [Set.indicator_of_mem hz]
      simpa only [Real.norm_eq_abs,Ψ] using
        abs_cavityGeneratedObservedRawFutureSuccessorExpectation_le D μ a W c γ j F L hL hbound _
    · rw [Set.indicator_of_notMem hz,norm_zero]; positivity
  have hs := Measure.ae_compProd_of_ae_fst
    (cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
      (W.measurable_clock c) (W.tree c)) W.measurableSet_supportSet hsupport
  have hv := cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a
    (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c) M
  have hp : ∀ᵐz ∂P,z.1.1∈W.supportSet ∧
      cavityGeneratedOriginCellValid (W.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) := by
    have hset : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
        CavityGeneratedOriginSelection (W.tree c) | z.1∈W.supportSet ∧
        cavityGeneratedOriginCellValid (W.clock z.1 c) (W.tree c)
          (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)} :=
      (W.measurableSet_supportSet.preimage measurable_fst).inter
        (measurableSet_cavityGeneratedRawOriginCellValid _ (W.measurable_clock c) (W.tree c))
    rw [show P=(M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
      (W.measurable_clock c) (W.tree c)) ⊗ₘ Kernel.const _ (parisiFreeMeasure μ a) by
        rw [Measure.compProd_const]]
    exact Measure.ae_compProd_of_ae_fst _ hset (hs.and hv)
  have he : A=ᵐ[P] fun z=>∑γ,(E γ).indicator (Ψ γ) z := by
    filter_upwards [hp] with z hz
    have hmasks σ := selectedFutureCell_of_valid D μ a (W.clock z.1.1 c) (W.tree c)
      (fun τ=>F (z.1.1,Function.update σ c τ)) j z.1.2 z.2 hz.2
    have hmask : A z=if z∈cavityGeneratedObservedRawFutureCellEvent W c j
        then cavityGeneratedObservedRawFutureSourceValue D μ a W c j F z else 0 := by
      unfold A cavityGeneratedObservedRawStreamingFutureCellSourceValue
      simp_rw [hmasks]
      simp only [cavityGeneratedObservedRawFutureCellEvent,mem_setOf_eq,
        cavityGeneratedRawOriginSelectionClock]
      split_ifs <;> simp only [integral_zero,cavityGeneratedObservedRawFutureSourceValue]
    rw [hmask]
    by_cases hc : z∈cavityGeneratedObservedRawFutureCellEvent W c j
    · rw [if_pos hc]
      let γ := cavityGeneratedObservedRawFuturePayloadChart (W.tree c) z.1.2
      have hg : z∈E γ :=
        (cavityGeneratedObservedRawFutureSourceEvent_iff_of_valid W c γ j z hz.1 hz.2).mpr ⟨rfl,hc⟩
      rw [Finset.sum_eq_single γ]
      · rw [Set.indicator_of_mem hg]
        exact (cavityGeneratedObservedRawFuture_forest_receiver D μ a W c γ j F z hg).symm
      · intro δ _ hδ
        have hnot : z∉E δ := by
          intro hd
          exact hδ ((cavityGeneratedObservedRawFutureSourceEvent_iff_of_valid W c δ j z hz.1 hz.2).mp hd).1.symm
        exact Set.indicator_of_notMem hnot (Ψ δ)
      · simp
    · rw [if_neg hc]
      symm; apply Finset.sum_eq_zero
      intro γ _
      exact Set.indicator_of_notMem
        (fun hg=>hc (cavityGeneratedObservedRawFutureSourceEvent_subset_cell W c γ j hg)) (Ψ γ)
  have hint : Integrable A P :=
    (integrable_finset_sum _ (fun γ _=>hi γ)).congr he.symm
  refine ⟨hint,?_⟩
  calc
    (∑γ,∫H,cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
        ∑γ,∫z,(E γ).indicator (Ψ γ) z ∂P := by
      apply Finset.sum_congr rfl
      intro γ _
      rw [cavityGeneratedObservedRawFutureSourceMeasure,cavityGeneratedRawOriginFutureSourceMeasure,
        integral_map (measurable_cavityGeneratedRawOriginFutureAppendedHistory
          (fun h=>W.clock h c) (W.measurable_clock c) (W.tree c)).aemeasurable
          (measurable_cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F hF).aestronglyMeasurable]
      change (∫z,Ψ γ z ∂P.restrict (E γ))=∫z,(E γ).indicator (Ψ γ) z ∂P
      exact (integral_indicator (measurableSet_cavityGeneratedObservedRawFutureSourceEvent W c γ j)).symm
    _ = ∫z,∑γ,(E γ).indicator (Ψ γ) z ∂P :=
      (integral_finset_sum _ (fun γ _=>hi γ)).symm
    _ = ∫z,A z ∂P := integral_congr_ae he.symm

theorem cavityGeneratedObservedRawStreamingFuture_source_partition
    (D : AnisotropicSpinModel (n+1)) (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [IsFiniteMeasure M]
    (hsupport : ∀ᵐh ∂M,h∈W.supportSet)
    (F : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedForestTerminalSample (n:=n) W.depth W.tree → ℝ)
    (hF : Measurable F) (L : ℝ) (hL : 0≤L) (hbound : ∀z,|F z|≤L) :
    Integrable (cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F)
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)) ∧
    (∑γ,∑j,∫H,cavityGeneratedObservedRawFutureSuccessorExpectation D μ a W c γ j F H
      ∂cavityGeneratedObservedRawFutureSourceMeasure μ a W c γ j M) =
    ∫z,cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F z
      ∂((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
        (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)) := by
  let P := (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a (fun h=>W.clock h c)
    (W.measurable_clock c) (W.tree c)).prod (parisiFreeMeasure μ a)
  have hj j := cavityGeneratedObservedRawStreamingFutureCell_source_partition
    D μ a W c M hsupport F hF L hL hbound j
  have he (z) : cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F z =
      ∑j : Fin (W.depth c),cavityGeneratedObservedRawStreamingFutureCellSourceValue D μ a W c F j z := by
    unfold cavityGeneratedObservedRawStreamingFutureSourceValue cavityGeneratedSelectedFuturePayload
    rw [integral_finset_sum _ (fun j _=>by
      simpa only [integrableOn_univ] using IntegrableOn.of_finite
        (μ:=(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1.1) : Measure _))
        (f:=fun σ=>cavityGeneratedSelectedFutureCellPayload D μ a (W.clock z.1.1 c) (W.tree c)
          (fun τ=>F (z.1.1,Function.update σ c τ)) j (z.1.2,z.2))
        (s:=Set.univ) Set.finite_univ)]
    simp only [cavityGeneratedObservedRawStreamingFutureCellSourceValue]
    exact (Fin.sum_univ_eq_sum_range (fun k : ℕ=>
      ∫σ,cavityGeneratedSelectedFutureCellPayload D μ a (W.clock z.1.1 c) (W.tree c)
        (fun τ=>F (z.1.1,Function.update σ c τ)) k (z.1.2,z.2)
        ∂(cavityGeneratedNativeForestTerminalProbability D μ a W.depth W.tree (W.clock z.1.1) : Measure _))
      (W.depth c)).symm
  have hefun : cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F =
      fun z=>∑j : Fin (W.depth c),cavityGeneratedObservedRawStreamingFutureCellSourceValue D μ a W c F j z :=
    funext he
  have hint : Integrable (cavityGeneratedObservedRawStreamingFutureSourceValue D μ a W c F) P := by
    rw [hefun]
    exact integrable_finset_sum _ (fun j _=>(hj j).1)
  refine ⟨hint,?_⟩
  rw [Finset.sum_comm]
  simp_rw [(hj _).2]
  rw [←integral_finset_sum _ (fun j _=>(hj j).1)]
  exact integral_congr_ae (.of_forall fun z=>(he z).symm)

end QuantitativeFollowup
