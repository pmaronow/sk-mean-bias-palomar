module
public import QuantitativeFollowup.FollowupCavityGeneratedCrossOriginFamilies
public import QuantitativeFollowup.FollowupCavityGeneratedSingleOriginChartCoverage

@[expose] public section

/-! The two selection kernels use the same original history. Their genuine
cells and the canonical order cases partition one double-selection law;
the common double-snoc map reconstructs its full history pushforward. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedCrossOriginChartActive (U : CavityGeneratedConstructedComponent m)
    (γ δ : PrintedGeneratedOriginChart U) (k : NativeStreamingGeneratedCrossEdgeChart)
    (r l : Paper.Overlap) : Prop := match γ, δ with
  | .inr (.inl i), .inr (.inl j) =>
      k.Holds (printedGeneratedOriginChartEdge U i).depth
        (printedGeneratedOriginChartEdge U j).depth r l
  | _, _ => k = .apart

theorem cavityGeneratedCrossOriginChartEvent_eq
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount)
    (γ δ : PrintedGeneratedOriginChart (W.component c))
    (k : NativeStreamingGeneratedCrossEdgeChart) :
    cavityGeneratedCrossOriginChartEvent W c γ δ k =
      {z : CavityGeneratedCrossOriginPayload W c |
        z.1 ∈ cavityGeneratedSingleOriginChartEvent W c γ ∧
        (z.1.1,z.2) ∈ cavityGeneratedSingleOriginChartEvent W c δ ∧
        cavityGeneratedCrossOriginChartActive (W.component c) γ δ k
          (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
          (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)} := rfl

theorem exists_cavityGeneratedCrossOriginChartActive
    (U : CavityGeneratedConstructedComponent m) (γ δ : PrintedGeneratedOriginChart U)
    (r l : Paper.Overlap) :
    ∃k, cavityGeneratedCrossOriginChartActive U γ δ k r l := by
  rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
  all_goals try exact ⟨.apart,rfl⟩
  change ∃k : NativeStreamingGeneratedCrossEdgeChart, k.Holds (printedGeneratedOriginChartEdge U i).depth
    (printedGeneratedOriginChartEdge U j).depth r l
  by_cases hd : (printedGeneratedOriginChartEdge U i).depth =
      (printedGeneratedOriginChartEdge U j).depth
  · rcases lt_trichotomy r l with hr | hr | hr
    · exact ⟨.lt,hd,hr⟩
    · exact ⟨.equal,hd,hr⟩
    · exact ⟨.gt,hd,hr⟩
  · exact ⟨.apart,hd⟩

theorem cavityGeneratedCrossOriginChartActive_unique
    (U : CavityGeneratedConstructedComponent m) (γ δ : PrintedGeneratedOriginChart U)
    (r l : Paper.Overlap) (k t : NativeStreamingGeneratedCrossEdgeChart)
    (hk : cavityGeneratedCrossOriginChartActive U γ δ k r l)
    (ht : cavityGeneratedCrossOriginChartActive U γ δ t r l) : k = t := by
  rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
  all_goals try exact hk.trans ht.symm
  change k.Holds (printedGeneratedOriginChartEdge U i).depth
    (printedGeneratedOriginChartEdge U j).depth r l at hk
  change t.Holds (printedGeneratedOriginChartEdge U i).depth
    (printedGeneratedOriginChartEdge U j).depth r l at ht
  cases k <;> cases t <;> simp_all [NativeStreamingGeneratedCrossEdgeChart.Holds]
  all_goals aesop (add safe forward lt_asymm)

theorem cavityGeneratedCrossOriginChartEvent_disjoint
    (W : CavityGeneratedConstructedForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on (fun x : PrintedGeneratedOriginChart (W.component c) ×
      (PrintedGeneratedOriginChart (W.component c) × NativeStreamingGeneratedCrossEdgeChart) =>
        cavityGeneratedCrossOriginChartEvent W c x.1 x.2.1 x.2.2)) := by
  intro x y hne
  rcases x with ⟨γ,δ,k⟩
  rcases y with ⟨γ',δ',t⟩
  apply Set.disjoint_left.mpr
  intro z hz hz'
  change z ∈ cavityGeneratedCrossOriginChartEvent W c γ δ k at hz
  change z ∈ cavityGeneratedCrossOriginChartEvent W c γ' δ' t at hz'
  rw [cavityGeneratedCrossOriginChartEvent_eq] at hz hz' 
  have hγ : γ = γ' := hz.1.1.symm.trans hz'.1.1
  have hδ : δ = δ' := hz.2.1.1.symm.trans hz'.2.1.1
  subst γ'
  subst δ'
  have hkt := cavityGeneratedCrossOriginChartActive_unique (W.component c) γ δ
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.1.2)
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2) k t hz.2.2 hz'.2.2
  subst t
  exact hne rfl

theorem cavityGeneratedCrossOriginChartEvent_cover_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h ∈ W.clockTemplate.orderSet) :
    ∀ᵐz ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst),
      ∃γ δ k,z ∈ cavityGeneratedCrossOriginChartEvent W c γ δ k := by
  have hp : MeasurableSet {z : CavityGeneratedCrossOriginPayload W c |
      ∃γ δ k,z ∈ cavityGeneratedCrossOriginChartEvent W c γ δ k} := by
    have hu := MeasurableSet.iUnion (fun γ => MeasurableSet.iUnion
      (fun δ => MeasurableSet.iUnion (measurableSet_cavityGeneratedCrossOriginChartEvent W c γ δ)))
    convert hu using 1
    ext z
    simp only [mem_setOf_eq,mem_iUnion]
  apply Measure.ae_compProd_of_ae_ae hp
  filter_upwards [cavityGeneratedSingleOriginChartEvent_cover_ae μ a W c M horder] with z hz
  obtain ⟨γ,hγ⟩ := hz
  have hh : z.1 ∈ W.clockTemplate.orderSet := hγ.2.1
  change ∀ᵐg ∂cavityGeneratedOriginSelectionKernel μ a W c z.1,
    ∃γ δ k,(z,g) ∈ cavityGeneratedCrossOriginChartEvent W c γ δ k
  filter_upwards [cavityGeneratedOriginSelectionKernel_ae_own_chart_cell μ a W c z.1 hh] with g hg
  let δ := cavityGeneratedOriginPayloadChart (W.component c) g
  have hδ : (z.1,g) ∈ cavityGeneratedSingleOriginChartEvent W c δ := ⟨rfl,hh,hg⟩
  obtain ⟨k,hk⟩ := exists_cavityGeneratedCrossOriginChartActive (W.component c) γ δ
    (cavityGeneratedOriginPayloadFreeClock (W.component c) z.2)
    (cavityGeneratedOriginPayloadFreeClock (W.component c) g)
  refine ⟨γ,δ,k,?_⟩
  rw [cavityGeneratedCrossOriginChartEvent_eq]
  exact ⟨hγ,hδ,hk⟩

theorem cavityGeneratedCrossOriginChartMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedConstructedForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (horder : ∀ᵐh ∂M,h ∈ W.clockTemplate.orderSet) :
    (∑γ,∑δ,∑k,cavityGeneratedCrossOriginChartMeasure μ a W c M γ δ k) =
      ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
        (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst).map
        (cavityGeneratedCrossOriginAppend W c) := by
  classical
  have hc : ∀ᵐz ∂((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst),
      ∃x : PrintedGeneratedOriginChart (W.component c) ×
        (PrintedGeneratedOriginChart (W.component c) × NativeStreamingGeneratedCrossEdgeChart),
        z ∈ cavityGeneratedCrossOriginChartEvent W c x.1 x.2.1 x.2.2 := by
    filter_upwards [cavityGeneratedCrossOriginChartEvent_cover_ae μ a W c M horder] with z hz
    rcases hz with ⟨γ,δ,k,hk⟩
    exact ⟨(γ,δ,k),hk⟩
  have hs := finiteMeasureChartPartition_sum_map_restrict
    ((M ⊗ₘ cavityGeneratedOriginSelectionKernel μ a W c) ⊗ₘ
      (cavityGeneratedOriginSelectionKernel μ a W c).comap Prod.fst measurable_fst)
    (fun x : PrintedGeneratedOriginChart (W.component c) ×
      (PrintedGeneratedOriginChart (W.component c) × NativeStreamingGeneratedCrossEdgeChart) =>
        cavityGeneratedCrossOriginChartEvent W c x.1 x.2.1 x.2.2)
    (fun x => measurableSet_cavityGeneratedCrossOriginChartEvent W c x.1 x.2.1 x.2.2)
    (cavityGeneratedCrossOriginChartEvent_disjoint W c) hc
    (cavityGeneratedCrossOriginAppend W c) (measurable_cavityGeneratedCrossOriginAppend W c)
  simpa only [Fintype.sum_prod_type,cavityGeneratedCrossOriginChartMeasure] using hs

end QuantitativeFollowup
