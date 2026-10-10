module
public import QuantitativeFollowup.SupportingPrintedCoalescedOriginWeights
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingOriginExpanded

@[expose] public section

/-! The genuine origin measure is dominated by one free draw per leaf
and its actual inherited fork charges. The bound does not count grid edges. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false

theorem printedGeneratedOriginLevel_child (q : ℕ → Paper.Overlap) {j : ℕ}
    {T : FiniteTerminalGenealogy j} (o : NativeStreamingOrigin T) :
    nativeStreamingOriginLevel q (nativeStreamingOriginChild o) =
      nativeStreamingOriginLevel q o := by cases o <;> rfl

theorem printedGeneratedOriginLevel_left (q : ℕ → Paper.Overlap) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (o : NativeStreamingOrigin T) :
    nativeStreamingOriginLevel q (nativeStreamingOriginLeft (U:=U) o) =
      nativeStreamingOriginLevel q o := by cases o <;> rfl

theorem printedGeneratedOriginLevel_right (q : ℕ → Paper.Overlap) {j : ℕ}
    {T U : FiniteTerminalGenealogy j} (o : NativeStreamingOrigin U) :
    nativeStreamingOriginLevel q (nativeStreamingOriginRight (T:=T) o) =
      nativeStreamingOriginLevel q o := by cases o <;> rfl

@[reducible] def printedGeneratedOriginForkDepths :
    {j : ℕ} → FiniteTerminalGenealogy j → List ℕ
  | _, .leaf => []
  | _, .advance T => printedGeneratedOriginForkDepths T
  | j, .fork T U => printedGeneratedOriginForkDepths T ++
      printedGeneratedOriginForkDepths U ++ [j]

theorem printedGeneratedOriginForkDepths_count {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (printedGeneratedOriginForkDepths T).length + 1 =
      FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
  induction T with
  | leaf => rfl
  | advance T ih => exact ih
  | fork T U ihT ihU =>
      simp only [printedGeneratedOriginForkDepths, List.length_append, List.length_singleton,
        asGenealogy, FiniteCascadeGenealogy.leafCount]
      omega

theorem printedGeneratedOriginBranchSum_eq_forkDepths
    (μ : Paper.ParisiMeasure) (q : ℕ → Paper.Overlap)
    {j : ℕ} (T : FiniteTerminalGenealogy j) (f : Paper.Overlap → ℝ) :
    nativeStreamingOriginBranchWeightSum μ q T (fun o => f (nativeStreamingOriginLevel q o)) =
      ((printedGeneratedOriginForkDepths T).map (fun d => Paper.parisiCDF μ (q d)*f (q d))).sum := by
  induction T with
  | leaf => rfl
  | advance T ih =>
      simpa only [nativeStreamingOriginBranchWeightSum, printedGeneratedOriginLevel_child,
        printedGeneratedOriginForkDepths] using ih
  | fork T U ihT ihU =>
      simp only [nativeStreamingOriginBranchWeightSum, printedGeneratedOriginLevel_left,
        printedGeneratedOriginLevel_right, nativeStreamingOriginLevel,
        FiniteCascadeRecordVertex.depth, ihT, ihU, printedGeneratedOriginForkDepths,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

theorem printedGeneratedOrigin_tail_partition (ν : Measure Paper.Overlap)
    (f : Paper.Overlap → ℝ) (hf : Integrable f ν)
    (lo hi : Paper.Overlap) (h : lo ≤ hi) :
    (∫r in Ioc lo hi, f r ∂ν) + (∫r in Ioc hi 1, f r ∂ν) =
      ∫r in Ioc lo 1, f r ∂ν := by
  have hd : Disjoint (Ioc lo hi) (Ioc hi (1 : Paper.Overlap)) := by
    apply disjoint_left.mpr
    intro r hr hs
    exact not_lt_of_ge hr.2 hs.1
  rw [←setIntegral_union hd measurableSet_Ioc hf.integrableOn hf.integrableOn,
    Ioc_union_Ioc_eq_Ioc h hi.property.2]

theorem printedGeneratedOriginEdgeIntegral_le_leaf_tail
    (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (f : Paper.Overlap → ℝ) (hf : Integrable f (parisiFreeMeasure μ a))
    (hpos : ∀r, 0 ≤ f r) :
    nativeStreamingOriginEdgeWeightIntegral μ a q T
      (fun o => f (nativeStreamingOriginLevel q o)) ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)*
        (∫r in Ioc (q j) 1, f r ∂parisiFreeMeasure μ a) := by
  induction T with
  | leaf =>
      simp only [nativeStreamingOriginEdgeWeightIntegral, nativeStreamingOriginLevel,
        FiniteCascadeRecordVertex.depth, hq0, asGenealogy, FiniteCascadeGenealogy.leafCount,
        Nat.cast_one, Ioc_self, Measure.restrict_empty, integral_zero_measure, mul_zero]
      rw [Paper.parisiCDF_eq_one_of_one_le μ (by norm_num)]
      simp
  | @advance j T ih =>
      simp only [nativeStreamingOriginEdgeWeightIntegral, printedGeneratedOriginLevel_child,
        nativeStreamingOriginLevel, asGenealogy, FiniteCascadeGenealogy.leafCount] at ⊢
      have hk : (1 : ℝ) ≤ FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
        exact_mod_cast FiniteCascadeGenealogy.leafCount_pos (asGenealogy T)
      have hn : 0 ≤ ∫r in Ioc (q (j+1)) (q j), f r ∂parisiFreeMeasure μ a :=
        integral_nonneg hpos
      have hs := mul_le_mul_of_nonneg_right hk hn
      simp only [one_mul] at hs
      have hp := printedGeneratedOrigin_tail_partition (parisiFreeMeasure μ a) f hf
        (q (j+1)) (q j) (hq (Nat.le_succ j))
      nlinarith only [ih, hs, hp]
  | @fork j T U ihT ihU =>
      simp only [nativeStreamingOriginEdgeWeightIntegral, printedGeneratedOriginLevel_left,
        printedGeneratedOriginLevel_right, asGenealogy, FiniteCascadeGenealogy.leafCount,
        Nat.cast_add]
      nlinarith only [ihT, ihU]

theorem printedGeneratedOrigin_total_free_partition (ν : Measure Paper.Overlap)
    (f : Paper.Overlap → ℝ) (hf : Integrable f ν) :
    ν.real {zeroOverlap}*f zeroOverlap + (∫r in Ioc zeroOverlap 1, f r ∂ν) = ∫r, f r ∂ν := by
  have hu : {zeroOverlap} ∪ Ioc zeroOverlap (1 : Paper.Overlap) = univ := by
    apply eq_univ_iff_forall.mpr
    intro r
    rcases eq_or_lt_of_le r.property.1 with hz | hp
    · left
      exact Subtype.ext hz.symm
    · right
      exact ⟨hp, r.property.2⟩
  have hd : Disjoint ({zeroOverlap} : Set Paper.Overlap) (Ioc zeroOverlap 1) := by
    apply disjoint_left.mpr
    rintro r hr hs
    have he : r = zeroOverlap := mem_singleton_iff.mp hr
    exact lt_irrefl zeroOverlap (he ▸ hs.1)
  rw [←smul_eq_mul, ←integral_singleton, ←setIntegral_union hd measurableSet_Ioc
      hf.integrableOn hf.integrableOn, hu, setIntegral_univ]

theorem printedGeneratedOriginClockBudget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a) (q : ℕ → Paper.Overlap)
    (hq : Antitone q) (hq0 : q 0 = 1) {j : ℕ} (T : FiniteTerminalGenealogy j)
    (hqj : q j = zeroOverlap) (f : Paper.Overlap → ℝ)
    (hf : Integrable f (parisiFreeMeasure μ a)) (hpos : ∀r, 0 ≤ f r) :
    nativeStreamingOriginWeightIntegral μ a q T a
      (fun o => f (nativeStreamingOriginLevel q o)) ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ)*(∫r, f r ∂parisiFreeMeasure μ a) +
      ((printedGeneratedOriginForkDepths T).map (fun d => Paper.parisiCDF μ (q d)*f (q d))).sum := by
  rw [nativeStreamingOriginWeightIntegral_eq_edges_branches_root,
    printedGeneratedOriginBranchSum_eq_forkDepths]
  have hedge := printedGeneratedOriginEdgeIntegral_le_leaf_tail μ a q hq hq0 T f hf hpos
  have hatom := nativeCoalescedIncomingMass_atom μ a ha hμ zeroOverlap
  rw [nativeCoalescedIncomingMass_zero] at hatom
  have hpart := printedGeneratedOrigin_total_free_partition (parisiFreeMeasure μ a) f hf
  have hk : (1 : ℝ) ≤ FiniteCascadeGenealogy.leafCount (asGenealogy T) := by
    exact_mod_cast FiniteCascadeGenealogy.leafCount_pos (asGenealogy T)
  have hn : 0 ≤ (parisiFreeMeasure μ a).real {zeroOverlap}*f zeroOverlap :=
    mul_nonneg measureReal_nonneg (hpos _)
  have hs := mul_le_mul_of_nonneg_right hk hn
  simp only [one_mul] at hs
  simp only [nativeStreamingOriginLevel, FiniteCascadeRecordVertex.depth, hqj] at ⊢ hedge
  rw [hatom, ←hpart]
  nlinarith only [hedge, hs]

end QuantitativeFollowup
