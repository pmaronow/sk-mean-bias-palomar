module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionCellSupport
public import QuantitativeFollowup.FollowupCavityGeneratedRawSourceMeasures

@[expose] public section

/-! Genuine Ioc support for actual raw origin selections. Both nested
cross draws use the original physical clock family and original tree. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m J : ℕ}

theorem measurableSet_cavityGeneratedRawOriginCellValid
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hclocks : ∀j, Measurable (fun h => q h j)) (T : FiniteTerminalGenealogy J) :
    MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection T |
      cavityGeneratedOriginCellValid (q z.1) T
        (cavityGeneratedOriginSelectionOrigin T z.2)} := by
  classical
  let H := CavityGeneratedHistory Paper.Overlap m
  let A := Fin (cavityGeneratedOriginForkVertices T).length
  let B := Fin (cavityGeneratedOriginEdges T).length × Paper.Overlap
  let f := fun z : H × CavityGeneratedOriginSelection T =>
    if cavityGeneratedOriginCellValid (q z.1) T
      (cavityGeneratedOriginSelectionOrigin T z.2) then (1 : ℝ) else 0
  have hf : Measurable (fun _ : H × A => (1 : ℝ)) := measurable_const
  have hr : Measurable (fun _ : H × Unit => (1 : ℝ)) := measurable_const
  have he : Measurable (fun z : H × B =>
      if z.2.2 ∈ Ioc
        (q z.1 (((cavityGeneratedOriginEdges T).get z.2.1).depth+1))
        (q z.1 ((cavityGeneratedOriginEdges T).get z.2.1).depth)
      then (1 : ℝ) else 0) := by
    have hi : Measurable (fun z : (H × Paper.Overlap) × Fin (cavityGeneratedOriginEdges T).length =>
        if z.1.2 ∈ Ioc
          (q z.1.1 (((cavityGeneratedOriginEdges T).get z.2).depth+1))
          (q z.1.1 ((cavityGeneratedOriginEdges T).get z.2).depth)
        then (1 : ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro i
      change Measurable (fun z : H × Paper.Overlap =>
        if z.2 ∈ Ioc
          (q z.1 (((cavityGeneratedOriginEdges T).get i).depth+1))
          (q z.1 ((cavityGeneratedOriginEdges T).get i).depth)
        then (1 : ℝ) else 0)
      have hq (j : ℕ) : Measurable (fun z : H × Paper.Overlap => q z.1 j) :=
        (hclocks j).comp measurable_fst
      have hs : MeasurableSet {z : H × Paper.Overlap |
          z.2 ∈ Ioc
            (q z.1 (((cavityGeneratedOriginEdges T).get i).depth+1))
            (q z.1 ((cavityGeneratedOriginEdges T).get i).depth)} := by
        convert (measurableSet_lt
          (hq (((cavityGeneratedOriginEdges T).get i).depth+1)) measurable_snd).inter
          (measurableSet_le measurable_snd
            (hq ((cavityGeneratedOriginEdges T).get i).depth)) using 1
        ext z
        simp only [mem_setOf_eq,mem_Ioc,mem_inter_iff]
      exact measurable_const.piecewise hs measurable_const
    exact hi.comp ((measurable_fst.prodMk (measurable_snd.comp measurable_snd)).prodMk
      (measurable_fst.comp measurable_snd))
  have hinner := (he.sumElim hr).comp (MeasurableEquiv.prodSumDistrib H B Unit).measurable
  have houter := (hf.sumElim hinner).comp
    (MeasurableEquiv.prodSumDistrib H A (B ⊕ Unit)).measurable
  have hm : Measurable f := by
    convert houter using 1
    funext z
    rcases z with ⟨h,g⟩
    rcases g with i | (z | u)
    all_goals simp only [f,cavityGeneratedOriginCellValid,cavityGeneratedOriginSelectionOrigin,ite_true]
    all_goals first | rfl | simp [Function.comp_def, MeasurableEquiv.prodSumDistrib,
      MeasurableEquiv.trans, MeasurableEquiv.sumCongr, MeasurableEquiv.prodComm,
      MeasurableEquiv.sumProdDistrib]
  have heq : {z : H × CavityGeneratedOriginSelection T |
      cavityGeneratedOriginCellValid (q z.1) T
        (cavityGeneratedOriginSelectionOrigin T z.2)} = {z | f z = 1} := by
    ext z
    by_cases hz : cavityGeneratedOriginCellValid (q z.1) T
      (cavityGeneratedOriginSelectionOrigin T z.2)
    all_goals simp [f,hz]
  rw [heq]
  exact measurableSet_eq_fun hm measurable_const

theorem cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀j, Measurable (fun h => q h j)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐz ∂M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T,
      cavityGeneratedOriginCellValid (q z.1) T (cavityGeneratedOriginSelectionOrigin T z.2) :=
  Measure.ae_compProd_of_ae_ae (measurableSet_cavityGeneratedRawOriginCellValid q hq T)
    (.of_forall fun h => cavityGeneratedOriginSelectionMeasure_ae_cell_valid μ a (q h) T a)

theorem cavityGeneratedRawOriginDoubleSelection_ae_cell_valid
    (μ : Paper.ParisiMeasure) (a : ℝ)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀j, Measurable (fun h => q h j)) (T : FiniteTerminalGenealogy J)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐz ∂cavityGeneratedRawOriginDoubleSelectionMeasure μ a q hq T M,
      cavityGeneratedOriginCellValid (q z.1.1) T (cavityGeneratedOriginSelectionOrigin T z.1.2) ∧
      cavityGeneratedOriginCellValid (q z.1.1) T (cavityGeneratedOriginSelectionOrigin T z.2) := by
  have hp := measurableSet_cavityGeneratedRawOriginCellValid q hq T
  have hf := cavityGeneratedRawOriginSelectionJointMeasure_ae_cell_valid μ a q hq T M
  have hboth : MeasurableSet {z : (CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection T) × CavityGeneratedOriginSelection T |
      cavityGeneratedOriginCellValid (q z.1.1) T (cavityGeneratedOriginSelectionOrigin T z.1.2) ∧
      cavityGeneratedOriginCellValid (q z.1.1) T (cavityGeneratedOriginSelectionOrigin T z.2)} :=
    (hp.preimage measurable_fst).inter
      (hp.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  apply Measure.ae_compProd_of_ae_ae hboth
  filter_upwards [hf] with z hz
  change ∀ᵐg ∂cavityGeneratedOriginSelectionMeasure μ a (q z.1) T a, _
  exact (cavityGeneratedOriginSelectionMeasure_ae_cell_valid μ a (q z.1) T a).mono
    (fun g hg => ⟨hz,hg⟩)

end QuantitativeFollowup
