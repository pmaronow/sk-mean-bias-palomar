module
public import QuantitativeFollowup.FollowupCavityGeneratedForestRefinement

@[expose] public section

/-! Actual attachment laws retain the complete old history and concentrate
on the literal appended clock. The prefix recovers the true weighted old
law; repeated vertex and endpoint marks need no supplied consistency
premise and no division by their atom masses. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {Q : Type*} [MeasurableSpace Q] [MeasurableSingletonClass Q]
variable {m : ℕ}

def cavityGeneratedHistoryPrefix (H : CavityGeneratedHistory Q (m+1)) :
    CavityGeneratedHistory Q m := fun i => H i.castSucc

theorem cavityGeneratedHistoryPrefix_measurable :
    Measurable (cavityGeneratedHistoryPrefix (Q:=Q) (m:=m)) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply i.castSucc

theorem cavityGeneratedHistoryPrefix_snoc (h : CavityGeneratedHistory Q m) (q : Q) :
    cavityGeneratedHistoryPrefix (Fin.snoc h q) = h := by
  funext i
  simp only [cavityGeneratedHistoryPrefix, Fin.snoc_castSucc]

theorem cavityGeneratedHistorySnoc_measurable
    (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
    Measurable (fun h : CavityGeneratedHistory Q m =>
      (Fin.snoc h (q h) : CavityGeneratedHistory Q (m+1))) := by
  exact cavityGeneratedHistoryAppend_measurable.comp (measurable_id.prodMk hq)

theorem cavityGeneratedHistorySnoc_prefix_law
    (M : Measure (CavityGeneratedHistory Q m))
    (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
    (M.map (fun h => (Fin.snoc h (q h) : CavityGeneratedHistory Q (m+1)))).map
      cavityGeneratedHistoryPrefix = M := by
  rw [Measure.map_map cavityGeneratedHistoryPrefix_measurable
    (cavityGeneratedHistorySnoc_measurable q hq)]
  have he : cavityGeneratedHistoryPrefix ∘
      (fun h : CavityGeneratedHistory Q m =>
        (Fin.snoc h (q h) : CavityGeneratedHistory Q (m+1))) = id := by
    funext h
    exact cavityGeneratedHistoryPrefix_snoc h (q h)
  rw [he, Measure.map_id]

theorem cavityGeneratedHistorySnoc_consistent [MeasurableEq Q]
    (M : Measure (CavityGeneratedHistory Q m))
    (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
    ∀ᵐ H ∂M.map (fun h => (Fin.snoc h (q h) : CavityGeneratedHistory Q (m+1))),
      H (Fin.last m) = q (cavityGeneratedHistoryPrefix H) := by
  have hp : MeasurableSet {H : CavityGeneratedHistory Q (m+1) |
      H (Fin.last m) = q (cavityGeneratedHistoryPrefix H)} :=
    measurableSet_eq_fun (measurable_pi_apply (Fin.last m))
      (hq.comp cavityGeneratedHistoryPrefix_measurable)
  apply (ae_map_iff (cavityGeneratedHistorySnoc_measurable q hq).aemeasurable hp).mpr
  exact Filter.Eventually.of_forall fun h => by
    rw [Fin.snoc_last, cavityGeneratedHistoryPrefix_snoc]

theorem cavityGeneratedFresh_prefix_law
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m)
    (E : Set (CavityGeneratedHistory Q m × Q)) :
    ((CavityGeneratedMarkProgram.fresh P E).measure ν).map cavityGeneratedHistoryPrefix =
      (((P.measure ν).prod ν).restrict E).map Prod.fst := by
  change ((((P.measure ν).prod ν).restrict E).map cavityGeneratedHistoryAppend).map
    cavityGeneratedHistoryPrefix = _
  rw [Measure.map_map cavityGeneratedHistoryPrefix_measurable
    cavityGeneratedHistoryAppend_measurable]
  have he : cavityGeneratedHistoryPrefix ∘
      (cavityGeneratedHistoryAppend (Q:=Q) (m:=m)) = Prod.fst := by
    funext z
    exact cavityGeneratedHistoryPrefix_snoc z.1 z.2
  rw [he]

theorem cavityGeneratedAtom_prefix_law
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m)
    (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
    ((CavityGeneratedMarkProgram.atom P q hq).measure ν).map cavityGeneratedHistoryPrefix =
      (P.measure ν).withDensity (fun h => ν {q h}) :=
  cavityGeneratedHistorySnoc_prefix_law _ q hq

theorem cavityGeneratedAtom_consistent [MeasurableEq Q]
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m)
    (q : CavityGeneratedHistory Q m → Q) (hq : Measurable q) :
    ∀ᵐ H ∂(CavityGeneratedMarkProgram.atom P q hq).measure ν,
      H (Fin.last m) = q (cavityGeneratedHistoryPrefix H) :=
  cavityGeneratedHistorySnoc_consistent _ q hq

theorem cavityGeneratedEndpointAtom_consistent [MeasurableEq Q]
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m) (q : Q) :
    ∀ᵐ H ∂(CavityGeneratedMarkProgram.atom P (fun _ => q) measurable_const).measure ν,
      H (Fin.last m) = q :=
  cavityGeneratedAtom_consistent ν P (fun _ => q) measurable_const

theorem cavityGeneratedInherited_prefix_law
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m) (i : Fin m)
    (k : ℕ) (w : CavityGeneratedHistory Q m → ℝ≥0∞) (hw : ∀h, w h ≤ k) :
    ((CavityGeneratedMarkProgram.inherited P i k w hw).measure ν).map
      cavityGeneratedHistoryPrefix = (P.measure ν).withDensity w :=
  cavityGeneratedHistorySnoc_prefix_law _ (fun h => h i) (measurable_pi_apply i)

theorem cavityGeneratedInherited_consistent [MeasurableEq Q]
    (ν : Measure Q) (P : CavityGeneratedMarkProgram Q m) (i : Fin m)
    (k : ℕ) (w : CavityGeneratedHistory Q m → ℝ≥0∞) (hw : ∀h, w h ≤ k) :
    ∀ᵐ H ∂(CavityGeneratedMarkProgram.inherited P i k w hw).measure ν,
      H (Fin.last m) = H i.castSucc := by
  exact cavityGeneratedHistorySnoc_consistent _ (fun h => h i) (measurable_pi_apply i)

theorem cavityGeneratedBranch_prefix_law
    (μ : Paper.ParisiMeasure) (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (i : Fin m) (l : ℕ) :
    ((cavityGeneratedBranchMarkProgram μ P i l).measure (parisiFreeMeasure μ a)).map
      cavityGeneratedHistoryPrefix =
      (P.measure (parisiFreeMeasure μ a)).withDensity (fun h =>
        parisiFreeMeasure μ a {h i} + cavityGeneratedBranchWeight μ i l h) := by
  rw [cavityGeneratedBranchMarkProgram_measure]
  exact cavityGeneratedHistorySnoc_prefix_law _ (fun h => h i) (measurable_pi_apply i)

theorem cavityGeneratedBranch_consistent
    (μ : Paper.ParisiMeasure) (a : ℝ) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (i : Fin m) (l : ℕ) :
    ∀ᵐ H ∂(cavityGeneratedBranchMarkProgram μ P i l).measure (parisiFreeMeasure μ a),
      H (Fin.last m) = H i.castSucc := by
  rw [cavityGeneratedBranchMarkProgram_measure]
  exact cavityGeneratedHistorySnoc_consistent _ (fun h => h i) (measurable_pi_apply i)

theorem CavityGeneratedClockLabel.append_reindex_value
    (l : CavityGeneratedClockLabel m) (H : CavityGeneratedHistory Paper.Overlap (m+1)) :
    (l.reindex Fin.castSucc).value H = l.value (cavityGeneratedHistoryPrefix H) :=
  CavityGeneratedClockLabel.reindex_value _ l _ H (fun _ => rfl)

theorem cavityGeneratedAtomClock_consistent
    (ν : Measure Paper.Overlap) (P : CavityGeneratedMarkProgram Paper.Overlap m)
    (l : CavityGeneratedClockLabel m) :
    ∀ᵐ H ∂(CavityGeneratedMarkProgram.atom P l.value l.continuous_value.measurable).measure ν,
      (CavityGeneratedClockLabel.mark (Fin.last m)).value H =
        (l.reindex Fin.castSucc).value H := by
  have he := cavityGeneratedAtom_consistent ν P l.value l.continuous_value.measurable
  exact he.mono fun H hh => by
    rw [CavityGeneratedClockLabel.append_reindex_value]
    exact hh

end QuantitativeFollowup
