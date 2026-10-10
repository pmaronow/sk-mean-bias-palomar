module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkMeasures
public import Mathlib.Data.Fin.Tuple.Basic

@[expose] public section

/-! Every normalized attachment preserves honest mark marginal budgets.
The history law is kept together with its appended mark, so old marks
remain joint with all later choices and order restrictions. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
variable {H Q : Type*} [MeasurableSpace H] [MeasurableSpace Q]
  [MeasurableSingletonClass Q] {m : ℕ}
set_option maxHeartbeats 800000

def cavityGeneratedExtendedMarks (marks : Fin m → H → Q) :
    Fin (m + 1) → H × Q → Q :=
  Fin.snoc (fun i z => marks i z.1) (fun z => z.2)

theorem cavityGeneratedExtendedMarks_measurable
    (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (i : Fin (m + 1)) : Measurable (cavityGeneratedExtendedMarks marks i) := by
  cases i using Fin.lastCases with
  | last => simpa only [cavityGeneratedExtendedMarks, Fin.snoc_last] using measurable_snd
  | cast i => simpa only [cavityGeneratedExtendedMarks, Fin.snoc_castSucc, Function.comp_def] using
      (hmarks i).comp measurable_fst

theorem cavityGenerated_smul_mono (ν : Measure Q) {c d : ℝ≥0∞}
    (hcd : c ≤ d) : c • ν ≤ d • ν := by
  apply Measure.le_iff.mpr
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul_left hcd _

theorem cavityGeneratedMarkBudget_fresh (ν : Measure Q) [SFinite ν]
    (hν : ν univ ≤ 1) (M : Measure H)
    (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C)
    (E : Set (H × Q)) :
    cavityGeneratedMarkBudget ν ((M.prod ν).restrict E)
      (cavityGeneratedExtendedMarks marks) C := by
  have hp : cavityGeneratedMarkBudget ν (M.prod ν)
      (cavityGeneratedExtendedMarks marks) C := by
    refine ⟨?_, ?_⟩
    · have hh : M.prod ν univ = M univ * ν univ := by
        simpa only [univ_prod_univ] using Measure.prod_prod (μ := M) (ν := ν) univ univ
      rw [hh]
      exact (mul_le_mul_right hν (M univ)).trans (by simpa only [mul_one] using hM.1)
    · intro i
      cases i using Fin.lastCases with
      | last =>
          simp only [cavityGeneratedExtendedMarks, Fin.snoc_last, Measure.map_snd_prod]
          exact cavityGenerated_smul_mono ν hM.1
      | cast i =>
          simp only [cavityGeneratedExtendedMarks, Fin.snoc_castSucc]
          change (M.prod ν).map (marks i ∘ Prod.fst) ≤ C • ν
          rw [← Measure.map_map (hmarks i) measurable_fst, Measure.map_fst_prod,
            Measure.map_smul (ν univ) (hmarks i).aemeasurable]
          exact (cavityGenerated_smul_mono (M.map (marks i)) hν).trans
            (by simpa only [one_smul] using hM.2 i)
  exact cavityGeneratedMarkBudget_mono ν _
    (cavityGeneratedExtendedMarks_measurable marks hmarks) C hp Measure.restrict_le_self

theorem cavityGeneratedMarkBudget_append_atom (ν : Measure Q) (hν : ν univ ≤ 1)
    (M : Measure H) (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C)
    (q : H → Q) (hq : Measurable q) :
    cavityGeneratedMarkBudget ν
      ((M.withDensity (fun h => ν {q h})).map (fun h => (h,q h)))
      (cavityGeneratedExtendedMarks marks) C := by
  have hp : Measurable (fun h => (h,q h)) := measurable_id.prodMk hq
  have he := cavityGenerated_atom_history_le ν hν M q
  refine ⟨?_, ?_⟩
  · rw [Measure.map_apply hp MeasurableSet.univ, preimage_univ]
    exact (he univ).trans hM.1
  · intro i
    cases i using Fin.lastCases with
    | last =>
        simp only [cavityGeneratedExtendedMarks, Fin.snoc_last]
        rw [Measure.map_map measurable_snd hp]
        change (M.withDensity (fun h => ν {q h})).map q ≤ C • ν
        exact (cavityGenerated_atom_marginal_le ν M q hq).trans
          (cavityGenerated_smul_mono ν hM.1)
    | cast i =>
        simp only [cavityGeneratedExtendedMarks, Fin.snoc_castSucc]
        change ((M.withDensity (fun h => ν {q h})).map (fun h => (h,q h))).map
          (marks i ∘ Prod.fst) ≤ C • ν
        rw [Measure.map_map ((hmarks i).comp measurable_fst) hp]
        change (M.withDensity (fun h => ν {q h})).map (marks i) ≤ C • ν
        exact (Measure.map_mono he (hmarks i)).trans (hM.2 i)

theorem cavityGeneratedMarkBudget_append_inherited (ν : Measure Q) (M : Measure H)
    (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C k : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C)
    (w : H → ℝ≥0∞) (hw : ∀h, w h ≤ k) (i : Fin m) :
    cavityGeneratedMarkBudget ν
      ((M.withDensity w).map (fun h => (h,marks i h)))
      (cavityGeneratedExtendedMarks marks) (k * C) := by
  have hp : Measurable (fun h => (h,marks i h)) := measurable_id.prodMk (hmarks i)
  have hW := cavityGeneratedMarkBudget_weight ν M marks hmarks C k hM w hw
  refine ⟨?_, ?_⟩
  · rw [Measure.map_apply hp MeasurableSet.univ, preimage_univ]
    exact hW.1
  · intro j
    cases j using Fin.lastCases with
    | last =>
        simp only [cavityGeneratedExtendedMarks, Fin.snoc_last]
        rw [Measure.map_map measurable_snd hp]
        exact hW.2 i
    | cast j =>
        simp only [cavityGeneratedExtendedMarks, Fin.snoc_castSucc]
        change ((M.withDensity w).map (fun h => (h,marks i h))).map
          (marks j ∘ Prod.fst) ≤ (k * C) • ν
        rw [Measure.map_map ((hmarks j).comp measurable_fst) hp]
        exact hW.2 j

end QuantitativeFollowup
