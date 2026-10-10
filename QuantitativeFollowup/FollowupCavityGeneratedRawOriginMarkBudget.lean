module
public import QuantitativeFollowup.FollowupCavityGeneratedRawOriginSelectionKernel
public import QuantitativeFollowup.FollowupCavityGeneratedAppendMarkPayloadBudget

@[expose] public section

/-! Raw selection keeps all unary observations in the actual genealogy.
The sharp budget uses antitone endpoint clocks only on source support,
and labels only the genuine fork vertices by inherited history marks. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128
variable {H : Type*} [MeasurableSpace H] {J m : ℕ}

theorem cavityGeneratedRawOriginSelectionKernel_mass_le
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (q : H → ℕ → Paper.Overlap) (hq : ∀d, Measurable (fun h => q h d))
    (T : FiniteTerminalGenealogy J) (h : H)
    (hanti : Antitone (q h)) (hzero : q h 0 = 1) :
    cavityGeneratedRawOriginSelectionKernel μ a q hq T h univ ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ≥0∞) := by
  have hm : Measurable (fun g => cavityGeneratedRawOriginSelectionClock q T (h,g)) :=
    (measurable_cavityGeneratedRawOriginSelectionClock q hq T).comp
      (measurable_const.prodMk measurable_id)
  have hs : a ≤ Paper.parisiCDF μ (q h J) :=
    scalarFloor_cdf_lower hμ (q h J).property.1
  have he := cavityGeneratedRawOriginSelectionKernel_clock_map μ a q hq T h hzero hs
  have hh := congrArg (fun M : Measure Paper.Overlap => M univ) he
  rw [Measure.map_apply hm MeasurableSet.univ, preimage_univ] at hh
  rw [hh, ←ofReal_measureReal,
    printedGeneratedOriginClockMeasure_mass μ a ha hμ (q h) hanti T a hs]
  exact (ENNReal.ofReal_le_ofReal (sub_le_self _ ha.1)).trans_eq (by simp)

theorem cavityGeneratedRawOriginForkClockMeasure_eq_history
    (μ : Paper.ParisiMeasure)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (T : FiniteTerminalGenealogy J)
    (idx : Fin (cavityGeneratedOriginForkVertices T).length → Fin m)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hfork : ∀i, q h ((cavityGeneratedOriginForkVertices T).get i).depth = h (idx i)) :
    printedGeneratedOriginForkClockMeasure μ (q h) T =
      ∑i : Fin (cavityGeneratedOriginForkVertices T).length,
        printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (h (idx i))) (h (idx i)) := by
  rw [cavityGeneratedOriginForkClockMeasure_eq_depths,
    ←cavityGeneratedOriginForkVertices_depths, List.map_map]
  let L := cavityGeneratedOriginForkVertices T
  let f := fun v : FiniteCascadeRecordVertex T =>
    printedGeneratedOriginClockRootMeasure (Paper.parisiCDF μ (q h v.depth)) (q h v.depth)
  have he : (L.map f).sum = ∑i : Fin L.length, f (L.get i) := by
    have hh := congrArg (fun A : List (FiniteCascadeRecordVertex T) => (A.map f).sum)
      (List.ofFn_get L)
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using hh.symm
  change (L.map f).sum = _
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f,L]
  rw [hfork i]

theorem cavityGeneratedRawOriginSelectionKernel_clock_domination
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (idx : Fin (cavityGeneratedOriginForkVertices T).length → Fin m)
    (h : CavityGeneratedHistory Paper.Overlap m)
    (hanti : Antitone (q h)) (hzero : q h 0 = 1) (htop : q h J = zeroOverlap)
    (hfork : ∀i, q h ((cavityGeneratedOriginForkVertices T).get i).depth = h (idx i)) :
    (cavityGeneratedRawOriginSelectionKernel μ a q hq T h).map
      (fun g => cavityGeneratedRawOriginSelectionClock q T (h,g)) ≤
      (FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ≥0∞) • parisiFreeMeasure μ a +
        ∑i : Fin (cavityGeneratedOriginForkVertices T).length, Measure.dirac (h (idx i)) := by
  rw [cavityGeneratedRawOriginSelectionKernel_clock_map μ a q hq T h hzero
    (scalarFloor_cdf_lower hμ (q h J).property.1)]
  have hd := printedGeneratedOriginClockMeasure_le_majorant μ a ha hμ
    (q h) hanti hzero T htop
  rw [printedGeneratedOriginClockMajorant,
    cavityGeneratedRawOriginForkClockMeasure_eq_history μ q T idx h hfork] at hd
  simp only [ENNReal.ofReal_natCast] at hd
  apply hd.trans
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  unfold printedGeneratedOriginClockRootMeasure
  exact (cavityGenerated_smul_mono (Measure.dirac (h (idx i)))
    ((ENNReal.ofReal_le_ofReal (Paper.parisiCDF_le_one μ (h (idx i)))).trans_eq (by simp))).trans_eq
      (one_smul _ _)

theorem cavityGeneratedRawOriginSelectionKernel_payload_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (idx : Fin (cavityGeneratedOriginForkVertices T).length → Fin m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, Antitone (q h) ∧ q h 0 = 1 ∧ q h J = zeroOverlap ∧
      ∀i, q h ((cavityGeneratedOriginForkVertices T).get i).depth = h (idx i)) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      (M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T)
      (cavityGeneratedPayloadExtendedMarks cavityGeneratedHistoryMarks
        (cavityGeneratedRawOriginSelectionClock q T))
      (((FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices T).length : ℝ≥0∞))*C) := by
  exact cavityGeneratedMarkBudget_payload_compProd (parisiFreeMeasure μ a) M
    (cavityGeneratedRawOriginSelectionKernel μ a q hq T) (cavityGeneratedRawOriginSelectionClock q T)
    (measurable_cavityGeneratedRawOriginSelectionClock q hq T)
    cavityGeneratedHistoryMarks cavityGeneratedHistoryMarks_measurable idx _ C hM
    (hsupport.mono fun h hh => cavityGeneratedRawOriginSelectionKernel_mass_le
      μ a ha hμ q hq T h hh.1 hh.2.1)
    (hsupport.mono fun h hh => cavityGeneratedRawOriginSelectionKernel_clock_domination
      μ a ha hμ q hq T idx h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)

theorem cavityGeneratedRawOriginSelectionKernel_appended_history_budget
    (μ : Paper.ParisiMeasure) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) 1)
    (hμ : μ ∈ scalarFloor a)
    (q : (CavityGeneratedHistory Paper.Overlap m) → ℕ → Paper.Overlap)
    (hq : ∀d, Measurable (fun h => q h d)) (T : FiniteTerminalGenealogy J)
    (idx : Fin (cavityGeneratedOriginForkVertices T).length → Fin m)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) [SFinite M]
    (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget (parisiFreeMeasure μ a) M cavityGeneratedHistoryMarks C)
    (hsupport : ∀ᵐh ∂M, Antitone (q h) ∧ q h 0 = 1 ∧ q h J = zeroOverlap ∧
      ∀i, q h ((cavityGeneratedOriginForkVertices T).get i).depth = h (idx i)) :
    cavityGeneratedMarkBudget (parisiFreeMeasure μ a)
      ((M ⊗ₘ cavityGeneratedRawOriginSelectionKernel μ a q hq T).map
        (fun z => Fin.snoc z.1 (cavityGeneratedRawOriginSelectionClock q T z)))
      cavityGeneratedHistoryMarks
      (((FiniteCascadeGenealogy.leafCount (asGenealogy T) : ℝ≥0∞) +
        ((cavityGeneratedOriginForkVertices T).length : ℝ≥0∞))*C) := by
  exact cavityGeneratedMarkBudget_kernel_payload_append (parisiFreeMeasure μ a) M
    (cavityGeneratedRawOriginSelectionKernel μ a q hq T) (cavityGeneratedRawOriginSelectionClock q T)
    (measurable_cavityGeneratedRawOriginSelectionClock q hq T) idx _ C hM
    (hsupport.mono fun h hh => cavityGeneratedRawOriginSelectionKernel_mass_le
      μ a ha hμ q hq T h hh.1 hh.2.1)
    (hsupport.mono fun h hh => cavityGeneratedRawOriginSelectionKernel_clock_domination
      μ a ha hμ q hq T idx h hh.1 hh.2.1 hh.2.2.1 hh.2.2.2)

end QuantitativeFollowup
