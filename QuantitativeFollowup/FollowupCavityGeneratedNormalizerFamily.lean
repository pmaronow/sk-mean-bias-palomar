module
public import QuantitativeFollowup.SupportingGeneratedNormalizerHistory
public import QuantitativeFollowup.SupportingGeneratedAppendBridge
public import QuantitativeFollowup.SupportingGeneratedForestLeafCounts
public import QuantitativeFollowup.FollowupCavityNativeSixStreamingGeneratedVertexPatternsConstruction

@[expose] public section

/-! The independent binary normalizer source for an actual history
measure. Its free draw and root attenuation preserve the budget; its
constructed forest adds exactly two leaves and retains the old history. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace QuantitativeFollowup
open FourPapersCommon QuantitativePaper FiniteTerminalGenealogy
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ}

def cavityGeneratedNormalizerFamilyMeasure (a : ℝ) (ν : Measure Paper.Overlap)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    Measure (CavityGeneratedHistory Paper.Overlap (m+1)) :=
  ENNReal.ofReal a • (M.prod ν).map cavityGeneratedHistoryAppend

theorem cavityGeneratedNormalizerFamilyMeasure_le (a : ℝ) (ha : a ≤ 1)
    (ν : Measure Paper.Overlap) (M : Measure (CavityGeneratedHistory Paper.Overlap m)) :
    cavityGeneratedNormalizerFamilyMeasure a ν M ≤ (M.prod ν).map cavityGeneratedHistoryAppend := by
  exact (cavityGenerated_smul_mono _ (ENNReal.ofReal_le_one.mpr ha)).trans_eq (one_smul _ _)

theorem cavityGeneratedNormalizerFamilyMeasure_budget
    (a : ℝ) (ha : a ≤ 1) (ν : Measure Paper.Overlap) [SFinite ν] (hν : ν univ ≤ 1)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M cavityGeneratedHistoryMarks C) :
    cavityGeneratedMarkBudget ν (cavityGeneratedNormalizerFamilyMeasure a ν M)
      cavityGeneratedHistoryMarks C := by
  have hp : cavityGeneratedMarkBudget ν (M.prod ν)
      (cavityGeneratedExtendedMarks cavityGeneratedHistoryMarks) C := by
    simpa only [Measure.restrict_univ] using
      cavityGeneratedMarkBudget_fresh ν hν M cavityGeneratedHistoryMarks
        cavityGeneratedHistoryMarks_measurable C hM univ
  have hb := cavityGeneratedMarkBudget_append_map ν (M.prod ν) C hp
  exact cavityGeneratedMarkBudget_mono ν _ cavityGeneratedHistoryMarks_measurable C hb
    (cavityGeneratedNormalizerFamilyMeasure_le a ha ν M)

theorem cavityGeneratedNormalizerFamilyMeasure_integral
    (a : ℝ) (ha : 0 ≤ a) (ν : Measure Paper.Overlap)
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (Φ : CavityGeneratedHistory Paper.Overlap (m+1) → ℝ) (hΦ : Measurable Φ) :
    (∫H,Φ H ∂cavityGeneratedNormalizerFamilyMeasure a ν M) =
      a*(∫z : CavityGeneratedHistory Paper.Overlap m × Paper.Overlap,
        Φ (Fin.snoc z.1 z.2) ∂M.prod ν) := by
  rw [cavityGeneratedNormalizerFamilyMeasure,integral_smul_measure,
    integral_map cavityGeneratedHistoryAppend_measurable.aemeasurable hΦ.aestronglyMeasurable,
    ENNReal.toReal_ofReal ha]
  rfl

theorem cavityGeneratedNormalizerFamily_leafCount (W : CavityGeneratedConstructedForest m) :
    cavityGeneratedForestLeafCount (printedGeneratedNormalizerAppendedForest W) =
      cavityGeneratedForestLeafCount W+2 := cavityGeneratedForestLeafCount_append_normalizer W

theorem cavityGeneratedNormalizerFamily_componentCount (W : CavityGeneratedConstructedForest m) :
    (printedGeneratedNormalizerAppendedForest W).componentCount = W.componentCount+1 := rfl

theorem cavityGeneratedNormalizerFamily_components_order {C : ℕ}
    (U : Fin C → CavityGeneratedConstructedComponent m)
    (H : CavityGeneratedHistory Paper.Overlap m)
    (hU : ∀c,H ∈ nativeStreamingGeneratedComponentOrderSet (U c)) :
    H ∈ (cavityGeneratedForestOfComponents U).clockTemplate.orderSet := by
  intro c j
  have hj0 : j.val ≤ (U c).depth := Nat.le_of_lt j.isLt
  have hj1 : j.val+1 ≤ (U c).depth := Nat.succ_le_of_lt j.isLt
  have hh := hU c j
  change (cavityGeneratedFiniteClockLabels (U c).label (j+1)).value H ≤
    (cavityGeneratedFiniteClockLabels (U c).label j).value H at hh
  change (if hd : j.val+1 ≤ (U c).depth then ((U c).label ⟨j.val+1,by omega⟩).value H else 0) ≤
    (if hd : j.val ≤ (U c).depth then ((U c).label ⟨j.val,by omega⟩).value H else 0)
  simpa only [cavityGeneratedFiniteClockLabels,dif_pos hj0,dif_pos hj1] using hh

theorem cavityGeneratedNormalizerFamily_snoc_order
    (W : CavityGeneratedConstructedForest m) (h : CavityGeneratedHistory Paper.Overlap m)
    (r : Paper.Overlap) (hh : h ∈ W.clockTemplate.orderSet) :
    Fin.snoc h r ∈ (printedGeneratedNormalizerAppendedForest W).clockTemplate.orderSet := by
  have ho : Fin.snoc h r ∈ (W.reindex Fin.castSucc).clockTemplate.orderSet := by
    rw [W.reindex_orderSet]
    change (Fin.snoc h r ∘ Fin.castSucc) ∈ W.clockTemplate.orderSet
    have he : Fin.snoc h r ∘ Fin.castSucc = h := by
      funext i
      simp only [Function.comp_apply,Fin.snoc_castSucc]
    rw [he]
    exact hh
  apply cavityGeneratedNormalizerFamily_components_order
  intro c
  cases c using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last]
      intro j
      fin_cases j
      · change (Fin.snoc (α:=fun _ : Fin (m+1) => Paper.Overlap) h r (Fin.last m)) ≤ 1
        rw [Fin.snoc_last]
        exact r.property.2
      · change 0 ≤ Fin.snoc (α:=fun _ : Fin (m+1) => Paper.Overlap) h r (Fin.last m)
        rw [Fin.snoc_last]
        exact r.property.1
  | cast c =>
      rw [Fin.snoc_castSucc]
      intro j
      have hj0 : j.val ≤ (W.reindex Fin.castSucc).depth c := Nat.le_of_lt j.isLt
      have hj1 : j.val+1 ≤ (W.reindex Fin.castSucc).depth c := Nat.succ_le_of_lt j.isLt
      have hj := ho c j
      change (if hd : j.val+1 ≤ (W.reindex Fin.castSucc).depth c then
        ((W.reindex Fin.castSucc).label c ⟨j.val+1,by omega⟩).value (Fin.snoc h r) else 0) ≤
        (if hd : j.val ≤ (W.reindex Fin.castSucc).depth c then
        ((W.reindex Fin.castSucc).label c ⟨j.val,by omega⟩).value (Fin.snoc h r) else 0) at hj
      simpa only [cavityGeneratedFiniteClockLabels,CavityGeneratedConstructedForest.component,
        dif_pos hj0,dif_pos hj1] using hj

theorem cavityGeneratedNormalizerFamily_order_ae
    (a : ℝ) (ha : a ≤ 1) (ν : Measure Paper.Overlap) [SFinite ν]
    (M : Measure (CavityGeneratedHistory Paper.Overlap m))
    (W : CavityGeneratedConstructedForest m) (hM : ∀ᵐh ∂M,h ∈ W.clockTemplate.orderSet) :
    ∀ᵐH ∂cavityGeneratedNormalizerFamilyMeasure a ν M,
      H ∈ (printedGeneratedNormalizerAppendedForest W).clockTemplate.orderSet := by
  have hs := (printedGeneratedNormalizerAppendedForest W).clockTemplate.isClosed_orderSet.measurableSet
  have hp : ∀ᵐz ∂M.prod ν,cavityGeneratedHistoryAppend z ∈
      (printedGeneratedNormalizerAppendedForest W).clockTemplate.orderSet := by
    apply (Measure.ae_prod_iff_ae_ae (hs.preimage cavityGeneratedHistoryAppend_measurable)).mpr
    exact hM.mono fun h hh => .of_forall fun r => cavityGeneratedNormalizerFamily_snoc_order W h r hh
  have hmap : ∀ᵐH ∂(M.prod ν).map cavityGeneratedHistoryAppend,
      H ∈ (printedGeneratedNormalizerAppendedForest W).clockTemplate.orderSet :=
    (ae_map_iff cavityGeneratedHistoryAppend_measurable.aemeasurable hs).mpr hp
  exact hmap.filter_mono (ae_mono (cavityGeneratedNormalizerFamilyMeasure_le a ha ν M))

end QuantitativeFollowup
