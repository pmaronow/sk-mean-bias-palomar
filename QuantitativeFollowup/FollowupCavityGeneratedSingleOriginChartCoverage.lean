module
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginFamilies

@[expose] public section

/-! The genuine single-origin payload lies in its own closed chart cell
almost everywhere. Actual old-order support then gives a full finite
chart cover, so one common history pushforward is reconstructed exactly. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

theorem cavityGeneratedOriginSelectionKernel_ae_own_chart_cell
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (hh : h ∈ W.clockTemplate.orderSet) :
    ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c h,
      printedGeneratedOriginChartCell (W.component c)
        (cavityGeneratedOriginPayloadChart (W.component c) g) h
        (cavityGeneratedOriginPayloadFreeClock (W.component c) g) := by
  classical
  let P := fun g : CavityGeneratedOriginSelection (W.tree c) =>
    printedGeneratedOriginChartCell (W.component c)
      (cavityGeneratedOriginPayloadChart (W.component c) g) h
      (cavityGeneratedOriginPayloadFreeClock (W.component c) g)
  have hm : MeasurableSet {g : CavityGeneratedOriginSelection (W.tree c) |
      ∃γ, (h,g)∈cavityGeneratedSingleOriginChartEvent W c γ} := by
    have hu : MeasurableSet (⋃γ,cavityGeneratedSingleOriginChartEvent W c γ) :=
      MeasurableSet.iUnion (measurableSet_cavityGeneratedSingleOriginChartEvent W c)
    have he : {g : CavityGeneratedOriginSelection (W.tree c) |
        ∃γ, (h,g)∈cavityGeneratedSingleOriginChartEvent W c γ} =
        (fun g => (h,g)) ⁻¹' (⋃γ,cavityGeneratedSingleOriginChartEvent W c γ) := by
      ext g
      simp only [mem_setOf_eq,mem_preimage,mem_iUnion]
    rw [he]
    exact hu.preimage (measurable_const.prodMk measurable_id)
  have hp : MeasurableSet {g | P g} := by
    convert hm using 1
    ext g
    constructor
    · intro hg
      exact ⟨cavityGeneratedOriginPayloadChart (W.component c) g,rfl,hh,hg⟩
    · rintro ⟨γ,hγ⟩
      change P g
      dsimp only [P]
      rw [hγ.1]
      exact hγ.2.2
  change ∀ᵐg ∂cavityGeneratedOriginSelectionMeasure μ a
    (W.clockTemplate.clock h c) (W.tree c) a, P g
  rw [cavityGeneratedOriginSelectionMeasure]
  simp only [ae_add_measure_iff,ae_finsetSum_measure_iff]
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_dirac_iff hp).mpr
    simp only [P,cavityGeneratedOriginPayloadChart,printedGeneratedOriginChartCell]
  · intro i _
    apply (ae_map_iff (measurable_cavityGeneratedOriginSelectionEdge (W.tree c) i).aemeasurable hp).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have he : W.clockTemplate.clock h c =
        nativeStreamingGeneratedComponentClock (W.component c) h :=
      printedGeneratedComponentClock_eq_native (W.component c) h
    change nativeStreamingGeneratedComponentClock (W.component c) h
        ((printedGeneratedOriginChartEdge (W.component c) i).depth+1) ≤ r ∧
      r ≤ nativeStreamingGeneratedComponentClock (W.component c) h
        (printedGeneratedOriginChartEdge (W.component c) i).depth
    rw [←he]
    exact ⟨hr.1.le,hr.2⟩
  · apply Measure.ae_smul_measure
    apply (ae_dirac_iff hp).mpr
    simp only [P,cavityGeneratedOriginPayloadChart,printedGeneratedOriginChartCell]

theorem cavityGeneratedSingleOriginChartEvent_cover_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet) :
    ∀ᵐz ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c),
      ∃γ,z∈cavityGeneratedSingleOriginChartEvent W c γ := by
  have hp : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      ∃γ,z∈cavityGeneratedSingleOriginChartEvent W c γ} := by
    have he : {z : CavityGeneratedHistory Paper.Overlap m ×
        CavityGeneratedOriginSelection (W.tree c) |
        ∃γ,z∈cavityGeneratedSingleOriginChartEvent W c γ} =
        ⋃γ,cavityGeneratedSingleOriginChartEvent W c γ := by
      ext z
      simp only [mem_setOf_eq,mem_iUnion]
    rw [he]
    exact MeasurableSet.iUnion (measurableSet_cavityGeneratedSingleOriginChartEvent W c)
  apply Measure.ae_compProd_of_ae_ae hp
  filter_upwards [horder] with h hh
  exact (cavityGeneratedOriginSelectionKernel_ae_own_chart_cell μ a W c h hh).mono
    (fun g hg=>⟨cavityGeneratedOriginPayloadChart (W.component c) g,rfl,hh,hg⟩)

theorem cavityGeneratedSingleOriginChartMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet) :
    (∑γ,cavityGeneratedSingleOriginChartMeasure μ a W c M γ) =
      (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            Fin.snoc (α := fun _ : Fin (m+1) => Paper.Overlap) z.1 (cavityGeneratedOriginSelectionClock W c z)) := by
  classical
  exact finiteMeasureChartPartition_sum_map_restrict
    (G := CavityGeneratedHistory Paper.Overlap (m+1))
    (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c)
    (cavityGeneratedSingleOriginChartEvent W c)
    (measurableSet_cavityGeneratedSingleOriginChartEvent W c)
    (cavityGeneratedSingleOriginChartEvent_disjoint W c)
    (cavityGeneratedSingleOriginChartEvent_cover_ae μ a W c M horder)
    (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            Fin.snoc (α := fun _ : Fin (m+1) => Paper.Overlap) z.1 (cavityGeneratedOriginSelectionClock W c z))
    (cavityGeneratedSingleOriginChart_append_measurable W c)

theorem cavityGeneratedSingleOriginChartMeasure_sum_withDensity
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (w : CavityGeneratedHistory Paper.Overlap (m+1)→ℝ≥0∞) :
    (∑γ,(cavityGeneratedSingleOriginChartMeasure μ a W c M γ).withDensity w) =
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            Fin.snoc (α := fun _ : Fin (m+1) => Paper.Overlap) z.1 (cavityGeneratedOriginSelectionClock W c z))).withDensity w := by
  classical
  rw [←cavityGeneratedSingleOriginChartMeasure_sum μ a W c M horder]
  simpa only [Measure.sum_fintype] using
    (withDensity_sum (fun γ => cavityGeneratedSingleOriginChartMeasure μ a W c M γ) w).symm

theorem integral_cavityGeneratedSingleOriginChartMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a∈Icc (0:ℝ) 1)
    (hμ : μ∈scalarFloor a) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    [IsFiniteMeasure M] (horder : ∀ᵐh ∂M,h∈W.clockTemplate.orderSet)
    (Φ : CavityGeneratedHistory Paper.Overlap (m+1)→ℝ) (hΦ : Measurable Φ)
    (C : ℝ) (hbound : ∀H,|Φ H|≤C) :
    (∑γ,∫H,Φ H ∂cavityGeneratedSingleOriginChartMeasure μ a W c M γ) =
      ∫H,Φ H ∂(M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
        (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            Fin.snoc (α := fun _ : Fin (m+1) => Paper.Overlap) z.1 (cavityGeneratedOriginSelectionClock W c z)) := by
  classical
  haveI := cavityGeneratedOriginSelectionKernel_finite μ a ha hμ W c
  let N := (M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c).map
    (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) =>
            Fin.snoc (α := fun _ : Fin (m+1) => Paper.Overlap) z.1 (cavityGeneratedOriginSelectionClock W c z))
  haveI : IsFiniteMeasure N := inferInstance
  have hi : Integrable Φ N := (integrable_const C).mono' hΦ.aestronglyMeasurable
    (.of_forall fun H=>by simpa only [Real.norm_eq_abs] using hbound H)
  have hc γ : Integrable Φ (cavityGeneratedSingleOriginChartMeasure μ a W c M γ) := by
    apply hi.mono_measure
    exact Measure.map_mono Measure.restrict_le_self
      (cavityGeneratedSingleOriginChart_append_measurable W c)
  rw [←cavityGeneratedSingleOriginChartMeasure_sum μ a W c M horder,
    integral_finsetSum_measure (fun γ _=>hc γ)]

end QuantitativeFollowup
