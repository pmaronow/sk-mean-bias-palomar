module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginChartCoverage
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload

@[expose] public section

/-! Selected edges genuinely lie in their half-open source cells. Both
nested selections retain the original history; their cell masks therefore
agree with raw callbacks, without callback measurability assumptions. -/
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

def cavityGeneratedOriginCellValid (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) : NativeStreamingOrigin T → Prop
  | .vertex _ => True
  | .edge e r => r ∈ Ioc (q (e.depth+1)) (q e.depth)

private theorem selectionCellValid_measurableSet
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J) :
    MeasurableSet {g : CavityGeneratedOriginSelection T |
      cavityGeneratedOriginCellValid q T (cavityGeneratedOriginSelectionOrigin T g)} := by
  have hm : Measurable (cavityGeneratedSelectedOriginPayload q T (fun _ => (1 : ℝ))) := by
    apply measurable_cavityGeneratedSelectedOriginPayload
    intro e
    exact measurable_const.piecewise measurableSet_Ioc measurable_const
  have he : {g : CavityGeneratedOriginSelection T |
      cavityGeneratedOriginCellValid q T (cavityGeneratedOriginSelectionOrigin T g)} =
      {g | cavityGeneratedSelectedOriginPayload q T (fun _ => (1 : ℝ)) g = 1} := by
    ext g
    rcases g with i | (z | u)
    · simp [cavityGeneratedOriginCellValid,cavityGeneratedOriginSelectionOrigin,
        cavityGeneratedSelectedOriginPayload,cavityGeneratedOriginCellMask]
    · by_cases hr : z.2 ∈ Ioc (q (((cavityGeneratedOriginEdges T).get z.1).depth+1))
          (q ((cavityGeneratedOriginEdges T).get z.1).depth)
      all_goals simp [cavityGeneratedOriginCellValid,cavityGeneratedOriginSelectionOrigin,
        cavityGeneratedSelectedOriginPayload,cavityGeneratedOriginCellMask,hr]
    · simp [cavityGeneratedOriginCellValid,cavityGeneratedOriginSelectionOrigin,
        cavityGeneratedSelectedOriginPayload,cavityGeneratedOriginCellMask]
  rw [he]
  exact measurableSet_eq_fun hm measurable_const

theorem cavityGeneratedOriginSelectionMeasure_ae_cell_valid
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (s : ℝ) :
    ∀ᵐg ∂cavityGeneratedOriginSelectionMeasure μ a q T s,
      cavityGeneratedOriginCellValid q T (cavityGeneratedOriginSelectionOrigin T g) := by
  have hp := selectionCellValid_measurableSet q T
  rw [cavityGeneratedOriginSelectionMeasure]
  simp only [ae_add_measure_iff,ae_finsetSum_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_dirac_iff hp).mpr
    trivial
  · intro i _
    apply (ae_map_iff (measurable_cavityGeneratedOriginSelectionEdge T i).aemeasurable hp).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hr
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff hp).mpr
    trivial

theorem cavityGeneratedOriginSelectionKernel_ae_cell_valid
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c h,
      cavityGeneratedOriginCellValid (W.clockTemplate.clock h c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) g) :=
  cavityGeneratedOriginSelectionMeasure_ae_cell_valid μ a (W.clockTemplate.clock h c) (W.tree c) a

theorem cavityGeneratedOriginCellMask_eq_raw_of_valid
    (q : ℕ → Paper.Overlap) (T : FiniteTerminalGenealogy J)
    (Φ : NativeStreamingOrigin T → ℝ) (o : NativeStreamingOrigin T)
    (ho : cavityGeneratedOriginCellValid q T o) :
    cavityGeneratedOriginCellMask q T Φ o = Φ o := by
  cases o with
  | vertex v => rfl
  | edge e r => exact if_pos ho

theorem cavityGeneratedSelectedOriginPayload_ae_eq_raw
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J) (s : ℝ) (Φ : NativeStreamingOrigin T → ℝ) :
    cavityGeneratedSelectedOriginPayload q T Φ =ᵐ[cavityGeneratedOriginSelectionMeasure μ a q T s]
      (fun g => Φ (cavityGeneratedOriginSelectionOrigin T g)) := by
  filter_upwards [cavityGeneratedOriginSelectionMeasure_ae_cell_valid μ a q T s] with g hg
  exact cavityGeneratedOriginCellMask_eq_raw_of_valid q T Φ _ hg

private theorem selectionCellValid_joint_measurableSet
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)} := by
  classical
  let H := CavityGeneratedHistory Paper.Overlap m
  let A := Fin (cavityGeneratedOriginForkVertices (W.tree c)).length
  let B := Fin (cavityGeneratedOriginEdges (W.tree c)).length × Paper.Overlap
  let f := fun z : H × CavityGeneratedOriginSelection (W.tree c) =>
    if cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1 c) (W.tree c)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2) then (1 : ℝ) else 0
  have hf : Measurable (fun _ : H × A => (1 : ℝ)) := measurable_const
  have hr : Measurable (fun _ : H × Unit => (1 : ℝ)) := measurable_const
  have he : Measurable (fun z : H × B =>
      if z.2.2 ∈ Ioc
        (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
        (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)
      then (1 : ℝ) else 0) := by
    have hi : Measurable (fun z : (H × Paper.Overlap) × Fin (cavityGeneratedOriginEdges (W.tree c)).length =>
        if z.1.2 ∈ Ioc
          (W.clockTemplate.clock z.1.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth+1))
          (W.clockTemplate.clock z.1.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth)
        then (1 : ℝ) else 0) := by
      apply measurable_from_prod_countable_left
      intro i
      change Measurable (fun z : H × Paper.Overlap =>
        if z.2 ∈ Ioc
          (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
          (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth)
        then (1 : ℝ) else 0)
      have hq (j : ℕ) : Measurable (fun z : H × Paper.Overlap => W.clockTemplate.clock z.1 c j) :=
        (W.clockTemplate.clock_continuous c j).measurable.comp measurable_fst
      have hs : MeasurableSet {z : H × Paper.Overlap |
          z.2 ∈ Ioc
            (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1))
            (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get i).depth)} := by
        convert (measurableSet_lt
          (hq (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1)) measurable_snd).inter
          (measurableSet_le measurable_snd
            (hq ((cavityGeneratedOriginEdges (W.tree c)).get i).depth)) using 1
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
  have heq : {z : H × CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)} = {z | f z = 1} := by
    ext z
    by_cases hz : cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1 c) (W.tree c)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)
    all_goals simp [f,hz]
  rw [heq]
  exact measurableSet_eq_fun hm measurable_const

theorem cavityGeneratedDoubleOriginSelection_ae_cell_valid
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐz ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst),
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) ∧
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2) := by
  have hp := selectionCellValid_joint_measurableSet W c
  have hf : ∀ᵐz ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c),
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2) :=
    Measure.ae_compProd_of_ae_ae hp (.of_forall (cavityGeneratedOriginSelectionKernel_ae_cell_valid μ a W c))
  have hboth : MeasurableSet {z : CavityGeneratedCrossOriginPayload W c |
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2) ∧
      cavityGeneratedOriginCellValid (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)} :=
    (hp.preimage measurable_fst).inter
      (hp.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  apply Measure.ae_compProd_of_ae_ae hboth
  filter_upwards [hf] with z hz
  change ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c z.1, _
  exact (cavityGeneratedOriginSelectionKernel_ae_cell_valid μ a W c z.1).mono
    (fun g hg => ⟨hz,hg⟩)

theorem cavityGeneratedDoubleSelectedOriginPayload_ae_eq_raw
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (Φ : CavityGeneratedHistory Paper.Overlap m →
      NativeStreamingOrigin (W.tree c) → NativeStreamingOrigin (W.tree c) → ℝ) :
    (fun z : CavityGeneratedCrossOriginPayload W c =>
      cavityGeneratedSelectedOriginPayload (W.clockTemplate.clock z.1.1 c) (W.tree c)
        (fun o => cavityGeneratedSelectedOriginPayload (W.clockTemplate.clock z.1.1 c) (W.tree c)
          (Φ z.1.1 o) z.2) z.1.2) =ᵐ[
        (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
          (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst]
      (fun z => Φ z.1.1 (cavityGeneratedOriginSelectionOrigin (W.tree c) z.1.2)
        (cavityGeneratedOriginSelectionOrigin (W.tree c) z.2)) := by
  filter_upwards [cavityGeneratedDoubleOriginSelection_ae_cell_valid μ a W c M] with z hz
  dsimp only [cavityGeneratedSelectedOriginPayload]
  rw [cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.1,
    cavityGeneratedOriginCellMask_eq_raw_of_valid _ _ _ _ hz.2]

end QuantitativeFollowup
