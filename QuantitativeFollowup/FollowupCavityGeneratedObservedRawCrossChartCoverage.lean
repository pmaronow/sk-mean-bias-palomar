module
public import QuantitativeFollowup.FollowupCavityGeneratedRawCrossObservation
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginCellSupport
public import QuantitativeFollowup.FollowupCavityGeneratedObservedRawSourceBudgets
public import FourPapersCommon.FiniteMeasureChartPartition

@[expose] public section

/-! The actual raw double-origin law is partitioned once. Both decoded
locations and clocks remain original; a non-EE pair uses only .apart,
while EE uses the genuine lt/equal/gt/apart chart partition. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

abbrev CavityGeneratedObservedRawCrossPayload (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) :=
  (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) ×
    CavityGeneratedOriginSelection (W.tree c)

private theorem rawCrossMeasurableSet_const {Z : Type*} [MeasurableSpace Z] (p : Prop) :
    MeasurableSet {z : Z | p} := by
  by_cases hp : p <;> simp only [hp, Set.setOf_true, Set.setOf_false]
  · exact MeasurableSet.univ
  · exact MeasurableSet.empty

def cavityGeneratedObservedRawCrossPayloadChart {J : ℕ} (T : FiniteTerminalGenealogy J) :
    CavityGeneratedOriginSelection T → CavityGeneratedObservedRawOriginChart T
  | .inl i => .inl i
  | .inr (.inl z) => .inr (.inl z.1)
  | .inr (.inr u) => .inr (.inr u)

theorem measurable_cavityGeneratedObservedRawCrossPayloadChart {J : ℕ} (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedObservedRawCrossPayloadChart T) := by
  apply measurable_fun_sum
  · exact measurable_inl
  · apply measurable_fun_sum
    · exact (measurable_inr.comp measurable_inl).comp measurable_fst
    · exact measurable_inr.comp measurable_inr

def cavityGeneratedObservedRawCrossFreeClock {J : ℕ} (T : FiniteTerminalGenealogy J) :
    CavityGeneratedOriginSelection T → Paper.Overlap
  | .inl _ => 0
  | .inr (.inl z) => z.2
  | .inr (.inr _) => 0

theorem measurable_cavityGeneratedObservedRawCrossFreeClock {J : ℕ} (T : FiniteTerminalGenealogy J) :
    Measurable (cavityGeneratedObservedRawCrossFreeClock T) :=
  measurable_const.sumElim (measurable_snd.sumElim measurable_const)

private theorem rawCrossChartSingleton {J : ℕ} (T : FiniteTerminalGenealogy J)
    (γ : CavityGeneratedObservedRawOriginChart T) : MeasurableSet ({γ} : Set (CavityGeneratedObservedRawOriginChart T)) := by
  rcases γ with i | (i | u)
  · have hh : MeasurableSet
        (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginForkVertices T).length)) :
          Set (CavityGeneratedObservedRawOriginChart T)) := (measurableSet_singleton i).inl_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet
        (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges T).length)) :
          Set (Fin (cavityGeneratedOriginEdges T).length ⊕ Unit)) :=
      (measurableSet_singleton i).inl_image
    have hh : MeasurableSet
        (Sum.inr '' (Sum.inl '' ({i} : Set (Fin (cavityGeneratedOriginEdges T).length))) :
          Set (CavityGeneratedObservedRawOriginChart T)) := hi.inr_image
    simpa only [Set.image_singleton] using hh
  · have hi : MeasurableSet (Sum.inr '' ({u} : Set Unit) :
        Set (Fin (cavityGeneratedOriginEdges T).length ⊕ Unit)) :=
      (measurableSet_singleton u).inr_image
    have hh : MeasurableSet (Sum.inr '' (Sum.inr '' ({u} : Set Unit)) :
        Set (CavityGeneratedObservedRawOriginChart T)) := hi.inr_image
    simpa only [Set.image_singleton] using hh

def rawCrossSingleEvent (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    Set (CavityGeneratedHistory Paper.Overlap m × CavityGeneratedOriginSelection (W.tree c)) :=
  {z | cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.2 = γ ∧
    z.1 ∈ W.supportSet ∧
    cavityGeneratedRawCrossCell (W.clock z.1 c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) γ)
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)}

private theorem rawCrossSingleEvent_measurable (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ : CavityGeneratedObservedRawOriginChart (W.tree c)) :
    MeasurableSet (rawCrossSingleEvent W c γ) := by
  have hclass : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.2 = γ} :=
    (rawCrossChartSingleton _ γ).preimage
      ((measurable_cavityGeneratedObservedRawCrossPayloadChart _).comp measurable_snd)
  have hold := W.measurableSet_supportSet.preimage
    (measurable_fst : Measurable (Prod.fst : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedHistory Paper.Overlap m))
  have hcell : MeasurableSet {z : CavityGeneratedHistory Paper.Overlap m ×
      CavityGeneratedOriginSelection (W.tree c) |
      cavityGeneratedRawCrossCell (W.clock z.1 c) (W.tree c)
        (cavityGeneratedRawCrossSite (W.tree c) γ)
        (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)} := by
    rcases γ with i | (i | u)
    · exact MeasurableSet.univ
    · have hr := (measurable_cavityGeneratedObservedRawCrossFreeClock (W.tree c)).comp
        (measurable_snd : Measurable (Prod.snd : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) → CavityGeneratedOriginSelection (W.tree c)))
      have hq (j : ℕ) : Measurable (fun z : CavityGeneratedHistory Paper.Overlap m ×
          CavityGeneratedOriginSelection (W.tree c) => W.clock z.1 c j) :=
        (W.measurable_clock c j).comp measurable_fst
      exact (measurableSet_le (measurable_subtype_coe.comp (hq _)) (measurable_subtype_coe.comp hr)).inter
        (measurableSet_le (measurable_subtype_coe.comp hr) (measurable_subtype_coe.comp (hq _)))
    · exact MeasurableSet.univ
  exact hclass.inter (hold.inter hcell)

def cavityGeneratedObservedRawCrossChartActive (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (r l : Paper.Overlap) : Prop :=
  match γ,δ with
  | .inr (.inl i), .inr (.inl j) => k.Holds
      ((cavityGeneratedOriginEdges (W.tree c)).get i).depth
      ((cavityGeneratedOriginEdges (W.tree c)).get j).depth r l
  | _,_ => k = .apart

def cavityGeneratedObservedRawCrossChartEvent (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) : Set (CavityGeneratedObservedRawCrossPayload W c) :=
  {z | z.1 ∈ rawCrossSingleEvent W c γ ∧ (z.1.1,z.2) ∈ rawCrossSingleEvent W c δ ∧
    cavityGeneratedObservedRawCrossChartActive W c γ δ k
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)}

theorem measurableSet_cavityGeneratedObservedRawCrossChartEvent
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart) :
    MeasurableSet (cavityGeneratedObservedRawCrossChartEvent W c γ δ k) := by
  have hf := (rawCrossSingleEvent_measurable W c γ).preimage
    (measurable_fst : Measurable (Prod.fst : CavityGeneratedObservedRawCrossPayload W c → _))
  have hs := (rawCrossSingleEvent_measurable W c δ).preimage
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd :
      Measurable (fun z : CavityGeneratedObservedRawCrossPayload W c => (z.1.1,z.2)))
  have ha : MeasurableSet {z : CavityGeneratedObservedRawCrossPayload W c |
      cavityGeneratedObservedRawCrossChartActive W c γ δ k
        (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
        (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)} := by
    have hr := (measurable_cavityGeneratedObservedRawCrossFreeClock (W.tree c)).comp
      (measurable_snd.comp measurable_fst : Measurable
        (fun z : CavityGeneratedObservedRawCrossPayload W c => z.1.2))
    have hl := (measurable_cavityGeneratedObservedRawCrossFreeClock (W.tree c)).comp
      (measurable_snd : Measurable (Prod.snd : CavityGeneratedObservedRawCrossPayload W c → _))
    rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
    all_goals try exact rawCrossMeasurableSet_const (k = .apart)
    cases k with
    | lt => exact ((rawCrossMeasurableSet_const _).inter
        (measurableSet_lt (measurable_subtype_coe.comp hr) (measurable_subtype_coe.comp hl)))
    | equal => exact (rawCrossMeasurableSet_const _).inter (measurableSet_eq_fun hr hl)
    | gt => exact ((rawCrossMeasurableSet_const _).inter
        (measurableSet_lt (measurable_subtype_coe.comp hl) (measurable_subtype_coe.comp hr)))
    | apart => exact rawCrossMeasurableSet_const _
  exact hf.inter (hs.inter ha)

def cavityGeneratedObservedRawCrossChartMeasure
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+2)) :=
  cavityGeneratedRawOriginCrossSourceMeasure μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c) M (cavityGeneratedObservedRawCrossChartEvent W c γ δ k)

theorem cavityGeneratedObservedRawCrossChartEvent_iff
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : CavityGeneratedObservedRawCrossPayload W c) :
    z ∈ cavityGeneratedObservedRawCrossChartEvent W c γ δ k ↔
      (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.1.2 = γ ∧
        z.1.1 ∈ W.supportSet ∧ cavityGeneratedRawCrossCell (W.clock z.1.1 c) (W.tree c)
          (cavityGeneratedRawCrossSite (W.tree c) γ)
          (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)) ∧
      (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.2 = δ ∧
        z.1.1 ∈ W.supportSet ∧ cavityGeneratedRawCrossCell (W.clock z.1.1 c) (W.tree c)
          (cavityGeneratedRawCrossSite (W.tree c) δ)
          (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)) ∧
      cavityGeneratedObservedRawCrossChartActive W c γ δ k
        (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
        (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2) := Iff.rfl

theorem cavityGeneratedObservedRawCrossChartEvent_holds
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (k : NativeStreamingGeneratedCrossEdgeChart)
    (z : CavityGeneratedObservedRawCrossPayload W c)
    (hz : z ∈ cavityGeneratedObservedRawCrossChartEvent W c γ δ k) :
    cavityGeneratedRawCrossChartHolds (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c) γ) (cavityGeneratedRawCrossSite (W.tree c) δ) k
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2) := by
  rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
  all_goals first | exact hz.2.2 | trivial

theorem cavityGeneratedObservedRawCrossPayloadChart_origin_eq
    {J : ℕ} (T : FiniteTerminalGenealogy J) (g : CavityGeneratedOriginSelection T)
    (γ : CavityGeneratedObservedRawOriginChart T)
    (hg : cavityGeneratedObservedRawCrossPayloadChart T g = γ) :
    cavityGeneratedRawCrossOrigin T (cavityGeneratedRawCrossSite T γ)
      (cavityGeneratedObservedRawCrossFreeClock T g) = cavityGeneratedOriginSelectionOrigin T g := by
  subst γ
  rcases g with i | (z | u) <;> rfl

theorem cavityGeneratedObservedRawCrossChartMeasure_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c))
    (k : NativeStreamingGeneratedCrossEdgeChart)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M] (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ k M) cavityGeneratedHistoryMarks
      ((((FiniteCascadeGenealogy.leafCount (asGenealogy (W.tree c)) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices (W.tree c)).length : ℝ≥0∞))^2)*C) :=
  cavityGeneratedObservedRawOriginCrossSourceMeasure_budget μ a ha hμ W c M C hM hsupport _

theorem exists_cavityGeneratedObservedRawCrossChartActive
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (r l : Paper.Overlap) :
    ∃k, cavityGeneratedObservedRawCrossChartActive W c γ δ k r l := by
  rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
  all_goals try exact ⟨.apart,rfl⟩
  change ∃k : NativeStreamingGeneratedCrossEdgeChart, k.Holds
    ((cavityGeneratedOriginEdges (W.tree c)).get i).depth
    ((cavityGeneratedOriginEdges (W.tree c)).get j).depth r l
  by_cases hd : ((cavityGeneratedOriginEdges (W.tree c)).get i).depth =
      ((cavityGeneratedOriginEdges (W.tree c)).get j).depth
  · rcases lt_trichotomy r l with hr | hr | hr
    · exact ⟨.lt,hd,hr⟩
    · exact ⟨.equal,hd,hr⟩
    · exact ⟨.gt,hd,hr⟩
  · exact ⟨.apart,hd⟩

theorem cavityGeneratedObservedRawCrossChartActive_unique
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount)
    (γ δ : CavityGeneratedObservedRawOriginChart (W.tree c)) (r l : Paper.Overlap)
    (k t : NativeStreamingGeneratedCrossEdgeChart)
    (hk : cavityGeneratedObservedRawCrossChartActive W c γ δ k r l)
    (ht : cavityGeneratedObservedRawCrossChartActive W c γ δ t r l) : k = t := by
  rcases γ with i | (i | u) <;> rcases δ with j | (j | v)
  all_goals try exact hk.trans ht.symm
  change k.Holds _ _ r l at hk
  change t.Holds _ _ r l at ht
  cases k <;> cases t <;> simp_all [NativeStreamingGeneratedCrossEdgeChart.Holds]
  all_goals aesop (add safe forward lt_asymm)

private theorem rawCross_cell_of_valid (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (h : CavityGeneratedHistory Paper.Overlap m)
    (g : CavityGeneratedOriginSelection (W.tree c))
    (hg : cavityGeneratedOriginCellValid (W.clock h c) (W.tree c)
      (cavityGeneratedOriginSelectionOrigin (W.tree c) g)) :
    cavityGeneratedRawCrossCell (W.clock h c) (W.tree c)
      (cavityGeneratedRawCrossSite (W.tree c)
        (cavityGeneratedObservedRawCrossPayloadChart (W.tree c) g))
      (cavityGeneratedObservedRawCrossFreeClock (W.tree c) g) := by
  rcases g with i | (z | u)
  · trivial
  · exact ⟨le_of_lt hg.1,hg.2⟩
  · trivial

theorem cavityGeneratedObservedRawCrossChartEvent_disjoint
    (W : CavityGeneratedObservedRawForest m) (c : Fin W.componentCount) :
    Pairwise (Disjoint on (fun x : CavityGeneratedObservedRawOriginChart (W.tree c) ×
      (CavityGeneratedObservedRawOriginChart (W.tree c) × NativeStreamingGeneratedCrossEdgeChart) =>
        cavityGeneratedObservedRawCrossChartEvent W c x.1 x.2.1 x.2.2)) := by
  intro x y hne
  rcases x with ⟨γ,δ,k⟩
  rcases y with ⟨γ',δ',t⟩
  apply Set.disjoint_left.mpr
  intro z hz hz'
  have hγ : γ = γ' := hz.1.1.symm.trans hz'.1.1
  have hδ : δ = δ' := hz.2.1.1.symm.trans hz'.2.1.1
  subst γ'
  subst δ'
  have hkt := cavityGeneratedObservedRawCrossChartActive_unique W c γ δ
    (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
    (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2) k t hz.2.2 hz'.2.2
  subst t
  exact hne rfl

theorem cavityGeneratedObservedRawCrossChartEvent_cover_ae
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    ∀ᵐz ∂cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c) M,
      ∃γ δ k, z ∈ cavityGeneratedObservedRawCrossChartEvent W c γ δ k := by
  let κ := cavityGeneratedRawOriginSelectionKernel μ a (fun h => W.clock h c)
    (W.measurable_clock c) (W.tree c)
  have hs : ∀ᵐz ∂M ⊗ₘ κ, z.1 ∈ W.supportSet :=
    Measure.ae_compProd_of_ae_fst κ W.measurableSet_supportSet hsupport
  have hh : ∀ᵐz ∂cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c) M, z.1.1 ∈ W.supportSet :=
    Measure.ae_compProd_of_ae_fst (κ.comap Prod.fst measurable_fst)
      (W.measurableSet_supportSet.preimage measurable_fst) hs
  filter_upwards [hh,cavityGeneratedRawOriginDoubleSelection_ae_cell_valid μ a
    (fun h => W.clock h c) (W.measurable_clock c) (W.tree c) M] with z hz hg
  let γ := cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.1.2
  let δ := cavityGeneratedObservedRawCrossPayloadChart (W.tree c) z.2
  obtain ⟨k,hk⟩ := exists_cavityGeneratedObservedRawCrossChartActive W c γ δ
    (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.1.2)
    (cavityGeneratedObservedRawCrossFreeClock (W.tree c) z.2)
  exact ⟨γ,δ,k,⟨rfl,hz,rawCross_cell_of_valid W c _ _ hg.1⟩,
    ⟨rfl,hz,rawCross_cell_of_valid W c _ _ hg.2⟩,hk⟩

theorem cavityGeneratedObservedRawCrossChartMeasure_sum
    (μ : Paper.ParisiMeasure) (a : ℝ) (W : CavityGeneratedObservedRawForest m)
    (c : Fin W.componentCount) (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (hsupport : ∀ᵐh ∂M, h ∈ W.supportSet) :
    (∑γ,∑δ,∑k,cavityGeneratedObservedRawCrossChartMeasure μ a W c γ δ k M) =
      (cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
        (W.measurable_clock c) (W.tree c) M).map
        (cavityGeneratedRawOriginDoubleAppendedHistory (fun h => W.clock h c) (W.tree c)) := by
  classical
  have hc : ∀ᵐz ∂cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c) M,
      ∃x : CavityGeneratedObservedRawOriginChart (W.tree c) ×
        (CavityGeneratedObservedRawOriginChart (W.tree c) × NativeStreamingGeneratedCrossEdgeChart),
        z ∈ cavityGeneratedObservedRawCrossChartEvent W c x.1 x.2.1 x.2.2 := by
    filter_upwards [cavityGeneratedObservedRawCrossChartEvent_cover_ae μ a W c M hsupport] with z hz
    rcases hz with ⟨γ,δ,k,hk⟩
    exact ⟨(γ,δ,k),hk⟩
  have hs := finiteMeasureChartPartition_sum_map_restrict
    (cavityGeneratedRawOriginDoubleSelectionMeasure μ a (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c) M)
    (fun x : CavityGeneratedObservedRawOriginChart (W.tree c) ×
      (CavityGeneratedObservedRawOriginChart (W.tree c) × NativeStreamingGeneratedCrossEdgeChart) =>
        cavityGeneratedObservedRawCrossChartEvent W c x.1 x.2.1 x.2.2)
    (fun x => measurableSet_cavityGeneratedObservedRawCrossChartEvent W c x.1 x.2.1 x.2.2)
    (cavityGeneratedObservedRawCrossChartEvent_disjoint W c) hc
    (cavityGeneratedRawOriginDoubleAppendedHistory (fun h => W.clock h c) (W.tree c))
    (measurable_cavityGeneratedRawOriginDoubleAppendedHistory (fun h => W.clock h c)
      (W.measurable_clock c) (W.tree c))
  simpa only [Fintype.sum_prod_type,cavityGeneratedObservedRawCrossChartMeasure,
    cavityGeneratedRawOriginCrossSourceMeasure] using hs

end QuantitativeFollowup

