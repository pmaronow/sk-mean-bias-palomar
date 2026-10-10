module
public import OverlapPaper.ReplicaSourceGroupKernel

@[expose] public section

/-! Exact baseline logarithmic averages for block-constant replica fields.
The vector mass is divided by the actual group size, so its exponent equals
the scalar Parisi mass. No baseline factorization is supplied as a premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open ColeHopfFoundation ColeHopfFoundation.ProbabilityTheory
open SpinGlass SpinGlass.Targets FourPapersCommon
open scoped BigOperators
namespace OverlapPaper

theorem sourceLogAverage_map {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (T : A → B) (hT : Measurable T) (a : ℝ)
    (f : B → ℝ) (hf : Measurable f) :
    sourceLogAverage (μ.map T) a f = sourceLogAverage μ a (fun x => f (T x)) := by
  by_cases ha : a = 0
  · simp only [sourceLogAverage, ha, ite_true]
    exact integral_map hT.aemeasurable hf.aestronglyMeasurable
  · simp only [sourceLogAverage, ha, ite_false]
    rw [integral_map hT.aemeasurable ((hf.const_mul a).exp.aestronglyMeasurable)]

theorem sourceLogAverage_scale {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (a c : ℝ) (hc : c ≠ 0) (f : A → ℝ) :
    sourceLogAverage μ a (fun x => c * f x) = c * sourceLogAverage μ (a * c) f := by
  by_cases ha : a = 0
  · simp [sourceLogAverage, ha, integral_const_mul]
  · have hac : a * c ≠ 0 := mul_ne_zero ha hc
    simp only [sourceLogAverage, ha, hac, ite_false, ← mul_assoc]
    field_simp

theorem sourceLogAverage_gaussianReal_eq_coleHopf (a : ℝ) (v : NNReal)
    (F : ℝ → ℝ) (hF : Measurable F) (x : ℝ) :
    sourceLogAverage (gaussianReal x v) a F = coleHopf a v F x := by
  have hm : (gaussianReal 0 v).map (fun z : ℝ => x + z) = gaussianReal x v := by
    simpa using gaussianReal_map_const_add (μ := 0) (v := v) x
  rw [← hm, sourceLogAverage_map _ _ (by fun_prop) a F hF]
  by_cases ha : a = 0
  · simp [sourceLogAverage, coleHopf, ha]
  · simp only [sourceLogAverage, coleHopf, ha, ite_false]
    ring

theorem mixedPotential_eq_schemeStep_logAverage {k : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) {p : ℕ} (hp : p ≤ k + 1) (x : ℝ) :
    mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q p, x) =
      sourceLogAverage (gaussianReal x (ξ.first (s.q (p + 1)) - ξ.first (s.q p)).toNNReal)
        (s.m p) (fun y => mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1), y)) := by
  rw [sourceLogAverage_gaussianReal_eq_coleHopf _ _ _
    (continuous_mixedPotential_section ξ _ _).measurable]
  rcases lt_or_eq_of_le (s.q_mono p hp) with hlt | he
  · exact mixedPotential_coleHopf_on_constantCDF ξ _
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
      ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩ hlt
      (fun _ hq => Paper.parisiCDF_scheme_cell s hp hq) x
  · simp [he]

theorem mixed_replica_group_baseline_step {k g d : ℕ}
    (ξ : AdmissibleEvenMixture) (s : RSBScheme k) (p : ℕ) (hp : p ≤ k + 1)
    (groupOf : Fin d → Fin g) (representative : Fin g → Fin d)
    (hrep : ∀ j, groupOf (representative j) = j) (c : ℝ) (hc : c ≠ 0)
    (x : Fin d → ℝ) :
    sourceLogAverage
      ((Measure.pi (fun j => gaussianReal (x (representative j))
        (ξ.first (s.q (p + 1)) - ξ.first (s.q p)).toNNReal)).map (replicaGroupCopy groupOf))
      (s.m p / c)
      (fun y => c * ∑ j, mixedPotential ξ (Paper.parisiSchemeMeasure s)
        (s.q (p + 1), y (representative j))) =
      c * ∑ j, mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q p, x (representative j)) := by
  have hb : s.q (p + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨s.q_nonneg (by omega), s.q_le_one (by omega)⟩
  have hm := (continuous_mixedPotential_section ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1))).measurable
  have hsum : Measurable (fun y : Fin d → ℝ => c * ∑ j : Fin g,
      mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1), y (representative j))) :=
    (Finset.measurable_fun_sum Finset.univ (fun j _ => hm.comp (measurable_pi_apply _))).const_mul c
  rw [sourceLogAverage_map _ _ (measurable_replicaGroupCopy groupOf) _ _ hsum]
  simp only [replicaGroupCopy, hrep]
  rw [sourceLogAverage_scale _ _ c hc, div_mul_cancel₀ _ hc]
  rw [sourceLogAverage_pi_sum _ (s.m p)
    (fun _ y => mixedPotential ξ (Paper.parisiSchemeMeasure s) (s.q (p + 1), y))
    (fun _ => hm)
    (fun _ => (mixedPotential_hasLinearGrowth ξ _ hb).toHasExpGrowth.integrable_gaussianReal hm.aestronglyMeasurable)
    (fun _ => ((mixedPotential_hasLinearGrowth ξ _ hb).exp_mul (s.m p)).integrable_gaussianReal
      ((hm.const_mul _).exp.aestronglyMeasurable))]
  simp_rw [← mixedPotential_eq_schemeStep_logAverage ξ s hp]

end OverlapPaper
