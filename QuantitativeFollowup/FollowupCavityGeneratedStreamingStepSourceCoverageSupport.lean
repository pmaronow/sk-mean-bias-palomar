module
public import QuantitativeFollowup.FollowupCavityGeneratedOriginSelectionKernel
public import QuantitativeFollowup.FollowupCavityGeneratedSelectedSourceSixPayload

@[expose] public section

/-! The actual origin payload is supported on its own original Ioc cell.
Consequently source masks agree with genuine callbacks almost everywhere;
no arbitrary version of an edge section is selected. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
variable {m : ℕ}
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
def cavityGeneratedStreamingOriginValid
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) : CavityGeneratedOriginSelection (W.tree c) → Prop
  | .inl _ => True
  | .inr (.inl z) => z.2∈Ioc
      (W.clockTemplate.clock h c (((cavityGeneratedOriginEdges (W.tree c)).get z.1).depth+1))
      (W.clockTemplate.clock h c ((cavityGeneratedOriginEdges (W.tree c)).get z.1).depth)
  | .inr (.inr _) => True

theorem measurableSet_cavityGeneratedStreamingOriginValid
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedStreamingOriginValid W c z.1 z.2} := by
  let H := CavityGeneratedHistory Paper.Overlap m
  let A := Fin (cavityGeneratedOriginForkVertices (W.tree c)).length
  let B := Fin (cavityGeneratedOriginEdges (W.tree c)).length × Paper.Overlap
  have hlo : Measurable (fun z : H × Fin (cavityGeneratedOriginEdges (W.tree c)).length =>
      W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth+1)) :=
    measurable_from_prod_countable_left (fun i=>by
      simpa only using (W.clockTemplate.clock_continuous c
        (((cavityGeneratedOriginEdges (W.tree c)).get i).depth+1)).measurable)
  have hhi : Measurable (fun z : H × Fin (cavityGeneratedOriginEdges (W.tree c)).length =>
      W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2).depth) :=
    measurable_from_prod_countable_left (fun i=>by
      simpa only using (W.clockTemplate.clock_continuous c
        ((cavityGeneratedOriginEdges (W.tree c)).get i).depth).measurable)
  have hecell : MeasurableSet {z : H×B | z.2.2∈Ioc
      (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
      (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)} :=
    (measurableSet_lt (f := fun z : H×B => W.clockTemplate.clock z.1 c
      (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
      (g := fun z : H×B => z.2.2)
      (hlo.comp (measurable_fst.prodMk measurable_snd.fst)) measurable_snd.snd).inter
      (measurableSet_le (f := fun z : H×B => z.2.2)
        (g := fun z : H×B => W.clockTemplate.clock z.1 c
          ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)
        measurable_snd.snd (hhi.comp (measurable_fst.prodMk measurable_snd.fst)))
  have he : Measurable (fun z : H×B => if z.2.2∈Ioc
      (W.clockTemplate.clock z.1 c (((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth+1))
      (W.clockTemplate.clock z.1 c ((cavityGeneratedOriginEdges (W.tree c)).get z.2.1).depth)
      then (1:ℝ) else 0) := measurable_const.ite hecell measurable_const
  have hi := (he.sumElim (measurable_const : Measurable (fun _ : H×Unit => (1:ℝ)))).comp
    (MeasurableEquiv.prodSumDistrib H B Unit).measurable
  have ho := ((measurable_const : Measurable (fun _ : H×A => (1:ℝ))).sumElim hi).comp
    (MeasurableEquiv.prodSumDistrib H A (B⊕Unit)).measurable
  have hm : Measurable (fun z : H×CavityGeneratedOriginSelection (W.tree c) =>
      if cavityGeneratedStreamingOriginValid W c z.1 z.2 then (1:ℝ) else 0) := by
    convert ho using 1
    funext z
    rcases z with ⟨h,g⟩
    rcases g with i | (i | u)
    all_goals simp only [cavityGeneratedStreamingOriginValid,ite_true]
    all_goals first | rfl | simp [Function.comp_def, MeasurableEquiv.prodSumDistrib,
      MeasurableEquiv.trans, MeasurableEquiv.sumCongr, MeasurableEquiv.prodComm,
      MeasurableEquiv.sumProdDistrib]
  have hset : {z : H×CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedStreamingOriginValid W c z.1 z.2} =
      {z | (if cavityGeneratedStreamingOriginValid W c z.1 z.2 then (1:ℝ) else 0)=1} := by
    ext z
    by_cases hz : cavityGeneratedStreamingOriginValid W c z.1 z.2 <;> simp [hz]
  rw [hset]
  exact measurableSet_eq_fun hm measurable_const

theorem cavityGeneratedStreamingOriginValid_kernel_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m) :
    ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c h,cavityGeneratedStreamingOriginValid W c h g := by
  have hp : MeasurableSet {g | cavityGeneratedStreamingOriginValid W c h g} :=
    (measurableSet_cavityGeneratedStreamingOriginValid W c).preimage (measurable_const.prodMk measurable_id)
  change ∀ᵐg ∂cavityGeneratedOriginSelectionMeasure μ a
    (W.clockTemplate.clock h c) (W.tree c) a,cavityGeneratedStreamingOriginValid W c h g
  rw [cavityGeneratedOriginSelectionMeasure]
  simp only [ae_add_measure_iff,ae_finsetSum_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i _
    apply Measure.ae_smul_measure
    exact (ae_dirac_iff hp).mpr trivial
  · intro i _
    apply (ae_map_iff (measurable_cavityGeneratedOriginSelectionEdge (W.tree c) i).aemeasurable hp).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    change r∈Ioc _ _
    exact hr
  · apply Measure.ae_smul_measure
    exact (ae_dirac_iff hp).mpr trivial


theorem cavityGeneratedStreamingOriginValid_compProd_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    ∀ᵐz ∂M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c,
      cavityGeneratedStreamingOriginValid W c z.1 z.2 := by
  apply Measure.ae_compProd_of_ae_ae (measurableSet_cavityGeneratedStreamingOriginValid W c)
  exact .of_forall (cavityGeneratedStreamingOriginValid_kernel_ae μ a W c)

theorem cavityGeneratedSelectedOriginPayload_eq_of_streaming_valid
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (h : CavityGeneratedHistory Paper.Overlap m) (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : cavityGeneratedStreamingOriginValid W c h g)
    (Φ : NativeStreamingOrigin (W.tree c) → ℝ) :
    cavityGeneratedSelectedOriginPayload (W.clockTemplate.clock h c) (W.tree c) Φ g =
      Φ (cavityGeneratedOriginSelectionOrigin (W.tree c) g) := by
  rcases g with i | (i | u)
  · rfl
  · exact if_pos hg
  · rfl

end QuantitativeFollowup
