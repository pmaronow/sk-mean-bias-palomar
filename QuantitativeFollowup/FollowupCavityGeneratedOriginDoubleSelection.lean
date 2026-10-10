module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel

@[expose] public section

/-! Both cross origins are sampled from the original component and
original history. The second kernel forgets the first payload; it does not
use the first enlarged tree. The honest budget is inherited twice. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedOriginSecondSelectionClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) × CavityGeneratedOriginSelection (W.tree c)) :
    Paper.Overlap := cavityGeneratedOriginSelectionClock W c (z.1.1,z.2)

theorem measurable_cavityGeneratedOriginSecondSelectionClock
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Measurable (cavityGeneratedOriginSecondSelectionClock W c) :=
  (measurable_cavityGeneratedOriginSelectionClock W c).comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem cavityGeneratedOriginDoubleSelection_payload_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M
      cavityGeneratedHistoryMarks C)
    (horder : ∀ᵐh ∂M, h ∈ W.clockTemplate.orderSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
        (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst)
      (cavityGeneratedPayloadExtendedMarks
        (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
          (cavityGeneratedOriginSelectionClock W c))
        (cavityGeneratedOriginSecondSelectionClock W c))
      ((((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkMarks W c).length : ℝ≥0∞))^2)*C) := by
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let κ := cavityGeneratedOriginSelectionKernel μ a W c
  let η : Kernel (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c)) (CavityGeneratedOriginSelection (W.tree c)) :=
    κ.comap Prod.fst measurable_fst
  let τ := cavityGeneratedOriginSelectionClock W c
  let marks := cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks τ
  let k : ℝ≥0∞ := FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c))
  let f := (cavityGeneratedOriginForkMarks W c).length
  have hb : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) (M ⊗ₘ κ) marks
      ((k+(f : ℝ≥0∞))*C) :=
    cavityGeneratedOriginSelectionKernel_payload_budget μ a ha hμ W c M C hM horder
  have hs : ∀ᵐz ∂M ⊗ₘ κ, z.1 ∈ W.clockTemplate.orderSet :=
    Measure.ae_compProd_of_ae_fst κ W.clockTemplate.isClosed_orderSet.measurableSet horder
  have hd : ∀ᵐz ∂M ⊗ₘ κ,
      (η z).map
        (fun g => cavityGeneratedOriginSecondSelectionClock W c (z,g)) ≤
          k • parisiFreeMeasure μ a +
            ∑i : Fin f, Measure.dirac
              (marks ((cavityGeneratedOriginForkMarks W c).get i).castSucc z) := by
    filter_upwards [hs] with z hz
    simpa only [κ,η,marks,τ,cavityGeneratedPayloadExtendedMarks,Fin.snoc_castSucc,
      cavityGeneratedHistoryMarks,cavityGeneratedOriginSecondSelectionClock,Kernel.comap_apply]
      using cavityGeneratedOriginSelectionKernel_clock_domination μ a ha hμ W c z.1 hz
  have hm : ∀ᵐz ∂M ⊗ₘ κ, η z univ ≤ k := by
    exact .of_forall fun z => cavityGeneratedOriginSelectionKernel_mass_le μ a ha hμ W c z.1
  have hh := cavityGeneratedMarkBudget_payload_compProd (parisiFreeMeasure μ a) (M ⊗ₘ κ)
    η (cavityGeneratedOriginSecondSelectionClock W c)
    (measurable_cavityGeneratedOriginSecondSelectionClock W c) marks
    (cavityGeneratedPayloadExtendedMarks_measurable cavityGeneratedHistoryMarks
      cavityGeneratedHistoryMarks_measurable τ
      (measurable_cavityGeneratedOriginSelectionClock W c))
    (fun i : Fin f => ((cavityGeneratedOriginForkMarks W c).get i).castSucc)
    k ((k+(f : ℝ≥0∞))*C) hb hm hd
  simpa only [κ,η,marks,τ,k,f,pow_two,mul_assoc] using hh

end QuantitativeFollowup
