module
public import QuantitativePaper.VectorMeasureOverlapScore
public import Mathlib.Probability.Moments.Variance

@[expose] public section

/-! The actual spin score has range length two and variance at most one. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
variable {n : ℕ}

theorem normalizedSpinScore_range (m : Field n) (σ : Configuration n) (hm : ∀ i, |m i| ≤ 1) :
    normalizedSpinScore m σ ∈ Icc (-(3/2 : ℝ)) (1/2 : ℝ) := by
  have hlo := (abs_le.mp (normalizedSpinScore_bound m σ hm)).1
  refine ⟨hlo, ?_⟩
  by_cases hn : n = 0
  · subst n
    norm_num [normalizedSpinScore]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : (∑ i : Fin n, (m i*Paper.spinSign (σ i)-(m i)^2/2)) ≤ ∑ _i : Fin n, (1/2 : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    have he : (Paper.spinSign (σ i))^2 = 1 := by rw [← sq_abs, Paper.abs_spinSign]; norm_num
    nlinarith [sq_nonneg (m i-Paper.spinSign (σ i))]
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  rw [normalizedSpinScore, fieldDot, EuclideanSpace.real_norm_sq_eq]
  apply (div_le_iff₀ hn0).mpr
  rw [Finset.sum_div]
  nlinarith

theorem vectorMeasureOverlapScore_range (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (q : Paper.Overlap) (z : VectorDisorderBrownianSample n × Configuration n) :
    vectorMeasureOverlapScore μ β t ht q z ∈ Icc (-(3/2 : ℝ)) (1/2 : ℝ) :=
  normalizedSpinScore_range _ _ (fun i => vectorMeasureSpinMean_component_bound μ β t ht q z.1 i)

theorem variance_vectorMeasureOverlapScore_le_one (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) :
    variance (vectorMeasureOverlapScore (n := n) μ β t ht q) (vectorMeasureSpinPathLaw μ β t a ht) ≤ 1 := by
  letI := vectorMeasureSpinPathLaw_probability (n := n) μ β t a ht
  have h := variance_le_sq_of_bounded
    (μ := vectorMeasureSpinPathLaw (n := n) μ β t a ht)
    (X := vectorMeasureOverlapScore (n := n) μ β t ht q)
    (.of_forall (vectorMeasureOverlapScore_range (n := n) μ β t ht q))
    (measurable_vectorMeasureOverlapScore μ β t ht q).aemeasurable
  norm_num at h
  exact h

end QuantitativePaper
