module
public import QuantitativeFollowup.FollowupCavityGeneratedMarkPrograms

@[expose] public section

/-! Total mass and every marginal of an explicit generated mark program
are bounded from its constructors. No mark-domination hypothesis is an
input to the program theorem. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace QuantitativeFollowup
variable {H G Q : Type*} [MeasurableSpace H] [MeasurableSpace G] [MeasurableSpace Q]
  [MeasurableSingletonClass Q]
set_option maxHeartbeats 1000000

theorem cavityGeneratedMarkBudget_map (ν : Measure Q) (M : Measure H)
    {m : ℕ} (marks : Fin m → H → Q) (newMarks : Fin m → G → Q)
    (hnewMarks : ∀i, Measurable (newMarks i)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M marks C)
    (f : H → G) (hf : Measurable f) (he : ∀i, newMarks i ∘ f = marks i) :
    cavityGeneratedMarkBudget ν (M.map f) newMarks C := by
  refine ⟨?_, ?_⟩
  · rw [Measure.map_apply hf MeasurableSet.univ, preimage_univ]
    exact hM.1
  · intro i
    rw [Measure.map_map (hnewMarks i) hf, he i]
    exact hM.2 i

theorem cavityGeneratedMarkBudget_append_map (ν : Measure Q)
    {m : ℕ} (M : Measure (CavityGeneratedHistory Q m × Q)) (C : ℝ≥0∞)
    (hM : cavityGeneratedMarkBudget ν M
      (cavityGeneratedExtendedMarks cavityGeneratedHistoryMarks) C) :
    cavityGeneratedMarkBudget ν (M.map cavityGeneratedHistoryAppend)
      cavityGeneratedHistoryMarks C := by
  apply cavityGeneratedMarkBudget_map ν M _ _
    (cavityGeneratedHistoryMarks_measurable (Q := Q)) C hM
    cavityGeneratedHistoryAppend cavityGeneratedHistoryAppend_measurable
  intro i
  funext z
  cases i using Fin.lastCases <;>
    simp only [Function.comp_apply, cavityGeneratedHistoryMarks,
      cavityGeneratedHistoryAppend, cavityGeneratedExtendedMarks,
      Fin.snoc_last, Fin.snoc_castSucc]

namespace CavityGeneratedMarkProgram

theorem actual_mark_budget (ν : Measure Q) [SFinite ν] (hν : ν univ ≤ 1)
    {m : ℕ} (P : CavityGeneratedMarkProgram Q m) :
    cavityGeneratedMarkBudget ν (P.measure ν)
      cavityGeneratedHistoryMarks (P.budget : ℝ≥0∞) := by
  induction P with
  | initial =>
      have hm : Measurable (fun q : Q => fun _ : Fin 1 => q) :=
        measurable_pi_lambda fun _ => measurable_id
      refine ⟨?_, ?_⟩
      · simpa only [measure, budget, Nat.cast_one, Measure.map_apply hm MeasurableSet.univ,
          preimage_univ] using hν
      · intro i
        simp only [measure, budget, Nat.cast_one, one_smul]
        rw [Measure.map_map (cavityGeneratedHistoryMarks_measurable i) hm]
        change ν.map id ≤ ν
        simpa only [Measure.map_id] using (le_rfl : ν ≤ ν)
  | fresh P E ih =>
      exact cavityGeneratedMarkBudget_append_map ν _ _
        (cavityGeneratedMarkBudget_fresh ν hν (P.measure ν) cavityGeneratedHistoryMarks
          cavityGeneratedHistoryMarks_measurable _ ih E)
  | atom P q hq ih =>
      have hh := cavityGeneratedMarkBudget_append_map ν _ _
        (cavityGeneratedMarkBudget_append_atom ν hν (P.measure ν) cavityGeneratedHistoryMarks
          cavityGeneratedHistoryMarks_measurable _ ih q hq)
      have hp : Measurable (fun h : CavityGeneratedHistory Q _ => (h,q h)) := by
        simpa only [id_eq] using measurable_id.prodMk hq
      rw [Measure.map_map cavityGeneratedHistoryAppend_measurable hp] at hh
      simpa only [measure, budget, Function.comp_def, cavityGeneratedHistoryAppend] using hh
  | inherited P i k w hw ih =>
      have hh := cavityGeneratedMarkBudget_append_map ν _ _
        (cavityGeneratedMarkBudget_append_inherited ν (P.measure ν) cavityGeneratedHistoryMarks
          cavityGeneratedHistoryMarks_measurable _ (k : ℝ≥0∞) ih w hw i)
      have hp : Measurable (fun h : CavityGeneratedHistory Q _ => (h,cavityGeneratedHistoryMarks i h)) := by
        simpa only [id_eq] using measurable_id.prodMk (cavityGeneratedHistoryMarks_measurable i)
      rw [Measure.map_map cavityGeneratedHistoryAppend_measurable hp] at hh
      simpa only [measure, budget, Nat.cast_mul, Function.comp_def,
        cavityGeneratedHistoryAppend, cavityGeneratedHistoryMarks] using hh
  | attenuate P w hw ih =>
      simpa only [measure, budget, one_mul] using cavityGeneratedMarkBudget_weight ν (P.measure ν)
        cavityGeneratedHistoryMarks cavityGeneratedHistoryMarks_measurable
        (P.budget : ℝ≥0∞) 1 ih w hw
  | restrict P E ih =>
      exact cavityGeneratedMarkBudget_mono ν cavityGeneratedHistoryMarks
        cavityGeneratedHistoryMarks_measurable _ ih Measure.restrict_le_self
  | add P R ihP ihR =>
      simpa only [measure, budget, Nat.cast_add] using cavityGeneratedMarkBudget_add ν (P.measure ν)
        (R.measure ν) cavityGeneratedHistoryMarks cavityGeneratedHistoryMarks_measurable
        (P.budget : ℝ≥0∞) (R.budget : ℝ≥0∞) ihP ihR

theorem measure_univ_le_budget (ν : Measure Q) [SFinite ν] (hν : ν univ ≤ 1)
    {m : ℕ} (P : CavityGeneratedMarkProgram Q m) :
    P.measure ν univ ≤ (P.budget : ℝ≥0∞) := (P.actual_mark_budget ν hν).1

theorem coordinate_marginal_le_budget (ν : Measure Q) [SFinite ν] (hν : ν univ ≤ 1)
    {m : ℕ} (P : CavityGeneratedMarkProgram Q m) (i : Fin m) :
    (P.measure ν).map (fun h => h i) ≤ (P.budget : ℝ≥0∞) • ν :=
  (P.actual_mark_budget ν hν).2 i

theorem isFiniteMeasure_measure (ν : Measure Q) [SFinite ν] (hν : ν univ ≤ 1)
    {m : ℕ} (P : CavityGeneratedMarkProgram Q m) : IsFiniteMeasure (P.measure ν) := by
  constructor
  apply (P.measure_univ_le_budget ν hν).trans_lt
  exact ENNReal.natCast_lt_top P.budget

theorem lintegral_coordinate_le_budget (ν : Measure Q) [SFinite ν] (hν : ν univ ≤ 1)
    {m : ℕ} (P : CavityGeneratedMarkProgram Q m) (i : Fin m)
    (χ : Q → ℝ≥0∞) (hχ : Measurable χ) :
    (∫⁻ h, χ (h i) ∂P.measure ν) ≤ (P.budget : ℝ≥0∞) * ∫⁻ q, χ q ∂ν := by
  have hi : Measurable (fun h : CavityGeneratedHistory Q m => h i) := measurable_pi_apply i
  rw [← lintegral_map hχ hi]
  calc
    (∫⁻ q, χ q ∂(P.measure ν).map (fun h => h i)) ≤
        ∫⁻ q, χ q ∂(P.budget : ℝ≥0∞) • ν :=
      lintegral_mono' (P.coordinate_marginal_le_budget ν hν i) le_rfl
    _ = (P.budget : ℝ≥0∞) * ∫⁻ q, χ q ∂ν :=
      lintegral_smul_measure (P.budget : ℝ≥0∞) χ

end CavityGeneratedMarkProgram

end QuantitativeFollowup
