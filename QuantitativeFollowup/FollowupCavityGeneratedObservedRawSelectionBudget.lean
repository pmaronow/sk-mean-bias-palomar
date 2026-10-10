module
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawProperties
public import QuantitativeFollowup.FollowupCavityGeneratedRawSourceMeasures

@[expose] public section

/-! The raw carrier supplies true fork labels on its computed support.
This instantiates the actual selection factories and derives their mark
budgets without a label on any unary observation. Both cross kernels use
the original history and original tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedObservedRawOriginSelectionKernel
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Kernel (CavityGeneratedHistory Paper.Overlap m) (CavityGeneratedOriginSelection (W.tree c)) :=
  cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)

def cavityGeneratedObservedRawOriginSelectionClock
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) →
      Paper.Overlap := cavityGeneratedRawOriginSelectionClock (fun h => W.clock h c) (W.tree c)

theorem measurable_cavityGeneratedObservedRawOriginSelectionClock
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Measurable (cavityGeneratedObservedRawOriginSelectionClock W c) :=
  measurable_cavityGeneratedRawOriginSelectionClock (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)

instance cavityGeneratedObservedRawOriginSelectionKernel_finite
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    IsFiniteKernel (cavityGeneratedObservedRawOriginSelectionKernel μ a W c) := by
  unfold cavityGeneratedObservedRawOriginSelectionKernel
  infer_instance

theorem cavityGeneratedObservedRawOriginSelectionKernel_mass_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    cavityGeneratedObservedRawOriginSelectionKernel μ a W c h univ ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) :=
  cavityGeneratedRawOriginSelectionKernel_mass_le μ a ha hμ
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) h
    (W.clock_antitone h c) (W.clock_terminal h c)

theorem cavityGeneratedObservedRawOriginSelectionKernel_clock_domination
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.supportSet) :
    (cavityGeneratedObservedRawOriginSelectionKernel μ a W c h).map
      (fun g => cavityGeneratedObservedRawOriginSelectionClock W c (h,g)) ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑i : Fin (cavityGeneratedOriginForkVertices (W.tree c)).length,
          Measure.dirac (h ((W.component c).forkMark i)) :=
  cavityGeneratedRawOriginSelectionKernel_clock_domination μ a ha hμ
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) (W.component c).forkMark h
    (W.clock_antitone h c) (W.clock_terminal h c) (W.clock_initial h c)
    ((W.component c).fork_clock_is_mark h (hh c))

theorem cavityGeneratedObservedRawOriginSelectionKernel_payload_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (M ⊗ₘ cavityGeneratedObservedRawOriginSelectionKernel μ a W c)
      (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
        (cavityGeneratedObservedRawOriginSelectionClock W c))
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  exact cavityGeneratedRawOriginSelectionKernel_payload_budget μ a ha hμ
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) (W.component c).forkMark M C hM
    (hsupport.mono fun h hh => ⟨W.clock_antitone h c, W.clock_terminal h c,
      W.clock_initial h c, (W.component c).fork_clock_is_mark h (hh c)⟩)

theorem cavityGeneratedObservedRawOriginSourceMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet)
    (E : Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c))) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedRawOriginSourceMeasure μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) M E) cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))*C) := by
  exact cavityGeneratedRawOriginSourceMeasure_budget μ a ha hμ
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) (W.component c).forkMark M C hM
    (hsupport.mono fun h hh => ⟨W.clock_antitone h c, W.clock_terminal h c,
      W.clock_initial h c, (W.component c).fork_clock_is_mark h (hh c)⟩) E

theorem cavityGeneratedObservedRawOriginDoubleSelection_payload_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) M)
      (cavityGeneratedPayloadExtendedMarks
        (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
          (cavityGeneratedObservedRawOriginSelectionClock W c))
        (cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c) (W.tree c)))
      ((((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))^2)*C) := by
  let κ := cavityGeneratedObservedRawOriginSelectionKernel μ a W c
  let η : Kernel (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) (CavityGeneratedOriginSelection (W.tree c)) :=
    κ.comap Prod.fst measurable_fst
  let τ := cavityGeneratedObservedRawOriginSelectionClock W c
  let marks := cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks τ
  let k : ℝ≥0∞ := FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))
  let f := (cavityGeneratedOriginForkVertices (W.tree c)).length
  have hb : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) (M ⊗ₘ κ) marks
      ((k+(f : ℝ≥0∞))*C) :=
    cavityGeneratedObservedRawOriginSelectionKernel_payload_budget μ a ha hμ W c M C hM hsupport
  have hs : ∀ᵐz ∂M ⊗ₘ κ, z.1 ∈ W.supportSet :=
    Measure.ae_compProd_of_ae_fst κ W.measurableSet_supportSet hsupport
  have hd : ∀ᵐz ∂M ⊗ₘ κ,
      (η z).map
        (fun g => cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c)
          (W.tree c) (z,g)) ≤ k • parisiFreeMeasure μ a +
            ∑i : Fin f, Measure.dirac (marks ((W.component c).forkMark i).castSucc z) := by
    filter_upwards [hs] with z hz
    simpa only [κ,η,marks,τ,cavityGeneratedPayloadExtendedMarks,Fin.snoc_castSucc,
      cavityGeneratedHistoryMarks,cavityGeneratedRawOriginSecondSelectionClock,
      cavityGeneratedObservedRawOriginSelectionClock,Kernel.comap_apply]
      using cavityGeneratedObservedRawOriginSelectionKernel_clock_domination μ a ha hμ W c z.1 hz
  have hm : ∀ᵐz ∂M ⊗ₘ κ, η z univ ≤ k :=
    .of_forall fun z => cavityGeneratedObservedRawOriginSelectionKernel_mass_le μ a ha hμ W c z.1
  have hh := cavityGeneratedMarkBudget_payload_compProd (parisiFreeMeasure μ a) (M ⊗ₘ κ)
    η (cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c) (W.tree c))
    (measurable_cavityGeneratedRawOriginSecondSelectionClock (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c)) marks
    (cavityGeneratedPayloadExtendedMarks_measurable cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable τ (measurable_cavityGeneratedObservedRawOriginSelectionClock W c))
    (fun i : Fin f => ((W.component c).forkMark i).castSucc)
    k ((k+(f : ℝ≥0∞))*C) hb hm hd
  simpa only [κ,η,marks,τ,k,f,cavityGeneratedRawOriginDoubleSelectionMeasure,
    cavityGeneratedObservedRawOriginSelectionKernel,pow_two,mul_assoc] using hh

end QuantitativeFollowup
