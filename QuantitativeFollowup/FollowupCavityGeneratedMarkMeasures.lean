module
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! Normalized attachment measures used in the generated three-defect
bound. An atom attachment is dominated by the actual mark measure,
even at a prescribed level. Fresh marks and inherited marks are treated
separately, so no coupling constant enters these structural budgets. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
variable {H Q : Type*} [MeasurableSpace H] [MeasurableSpace Q]
set_option maxHeartbeats 700000

theorem cavityGenerated_atom_measure_le (ν : Measure Q) (q : Q) :
    ν {q} • Measure.dirac q ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
  by_cases hq : q ∈ s
  · simpa only [Set.indicator_of_mem hq, Pi.one_apply, mul_one] using
      (measure_mono (singleton_subset_iff.mpr hq) : ν {q} ≤ ν s)
  · simp only [Set.indicator_of_notMem hq, mul_zero, zero_le]

theorem cavityGenerated_atom_marginal_le (ν : Measure Q) (M : Measure H)
    (q : H → Q) (hq : Measurable q) :
    (M.withDensity (fun h => ν {q h})).map q ≤ M univ • ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hq hs, withDensity_apply _ (hq hs),
    Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ h in q ⁻¹' s, ν {q h} ∂M) ≤ ∫⁻ h in q ⁻¹' s, ν s ∂M := by
      apply setLIntegral_mono' (hq hs)
      intro h hh
      exact measure_mono (singleton_subset_iff.mpr hh)
    _ = ν s * M (q ⁻¹' s) := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ ≤ ν s * M univ := mul_le_mul_right (measure_mono (subset_univ _)) _
    _ = M univ * ν s := mul_comm _ _

theorem cavityGenerated_withDensity_le (M : Measure H) (w : H → ℝ≥0∞)
    (k : ℝ≥0∞) (hw : ∀h, w h ≤ k) : M.withDensity w ≤ k • M := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, smul_eq_mul]
  calc
    (∫⁻ h in s, w h ∂M) ≤ ∫⁻ _ in s, k ∂M := lintegral_mono hw
    _ = k * M s := by simp only [lintegral_const, Measure.restrict_apply_univ]

theorem cavityGenerated_atom_history_le (ν : Measure Q) (hν : ν univ ≤ 1)
    (M : Measure H) (q : H → Q) :
    M.withDensity (fun h => ν {q h}) ≤ M := by
  simpa only [one_smul] using cavityGenerated_withDensity_le M (fun h => ν {q h}) 1
    (fun h => (measure_mono (subset_univ _)).trans hν)

def cavityGeneratedMarkBudget (ν : Measure Q) (M : Measure H)
    {m : ℕ} (marks : Fin m → H → Q) (C : ℝ≥0∞) : Prop :=
  M univ ≤ C ∧ ∀i, M.map (marks i) ≤ C • ν

theorem cavityGeneratedMarkBudget_mono (ν : Measure Q) {M N : Measure H}
    {m : ℕ} (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C) (hNM : N ≤ M) :
    cavityGeneratedMarkBudget ν N marks C := by
  exact ⟨(hNM _).trans hM.1, fun i =>
    (Measure.map_mono hNM (hmarks i)).trans (hM.2 i)⟩

theorem cavityGeneratedMarkBudget_add (ν : Measure Q) (M N : Measure H)
    {m : ℕ} (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C D : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C)
    (hN : cavityGeneratedMarkBudget ν N marks D) :
    cavityGeneratedMarkBudget ν (M + N) marks (C + D) := by
  refine ⟨?_, ?_⟩
  · rw [Measure.add_apply]
    exact add_le_add hM.1 hN.1
  · intro i
    rw [Measure.map_add _ _ (hmarks i), add_smul]
    exact add_le_add (hM.2 i) (hN.2 i)

theorem cavityGeneratedMarkBudget_weight (ν : Measure Q) (M : Measure H)
    {m : ℕ} (marks : Fin m → H → Q) (hmarks : ∀i, Measurable (marks i))
    (C k : ℝ≥0∞) (hM : cavityGeneratedMarkBudget ν M marks C)
    (w : H → ℝ≥0∞) (hw : ∀h, w h ≤ k) :
    cavityGeneratedMarkBudget ν (M.withDensity w) marks (k * C) := by
  have he := cavityGenerated_withDensity_le M w k hw
  refine ⟨?_, ?_⟩
  · apply (he univ).trans
    rw [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul_right hM.1 k
  · intro i
    apply (Measure.map_mono he (hmarks i)).trans
    rw [Measure.map_smul k (hmarks i).aemeasurable]
    calc
      k • M.map (marks i) ≤ k • (C • ν) := by
        apply Measure.le_iff.mpr
        intro s hs
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_right (hM.2 i s) k
      _ = (k * C) • ν := by rw [smul_smul]

end QuantitativeFollowup
