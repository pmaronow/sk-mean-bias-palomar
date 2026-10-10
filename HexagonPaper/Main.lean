module
public import QuantitativeFollowup.FollowupNativeMainResults

@[expose] public section

/-! Main theorem and its elementary changes of normalization for the
revised upper-bound manuscript. The imported result is the already proved
actual SK model theorem, with its budget discharged internally. No external
variance asymptotic or PositiveLaplaceWindow hypothesis is used. -/

noncomputable section
open QuantitativeFollowup QuantitativePaper

namespace HexagonPaper

/-- Hexagon Theorem 1.1: the literal mean-bias bound for every N >= 2. -/
theorem main_mean_bias (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  exact QuantitativeFollowup.improved_native_bias β hβ

/-- The free-energy-density correction is the same gap divided by β. -/
theorem free_energy_density_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β / β ∧
        finiteBias n β / β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  obtain ⟨C, hC, hAll⟩ := main_mean_bias β hβ
  have hβp : 0 < β := lt_trans zero_lt_one hβ
  refine ⟨C / β, div_pos hC hβp, ?_⟩
  intro n hn
  refine ⟨div_nonneg (hAll n hn).1 hβp.le, ?_⟩
  simpa only [div_mul_eq_mul_div] using
    div_le_div_of_nonneg_right (hAll n hn).2 hβp.le

/-- The unnormalized expected log-partition gap has order N^(3/10). -/
theorem log_partition_mean_correction (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ (n : ℝ) * finiteBias n β ∧
        (n : ℝ) * finiteBias n β ≤ C * (n : ℝ) ^ (3 / 10 : ℝ) := by
  obtain ⟨C, hC, hAll⟩ := main_mean_bias β hβ
  refine ⟨C, hC, ?_⟩
  intro n hn
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : (n : ℝ) * (n : ℝ) ^ (-(7 / 10 : ℝ)) =
      (n : ℝ) ^ (3 / 10 : ℝ) := by
    calc
      _ = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
        rw [Real.rpow_one]
      _ = (n : ℝ) ^ ((1 : ℝ) + (-(7 / 10 : ℝ))) :=
        (Real.rpow_add hnp _ _).symm
      _ = _ := by norm_num
  refine ⟨mul_nonneg hnp.le (hAll n hn).1, ?_⟩
  calc
    (n : ℝ) * finiteBias n β ≤
        (n : ℝ) * (C * (n : ℝ) ^ (-(7 / 10 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hAll n hn).2 hnp.le
    _ = C * ((n : ℝ) * (n : ℝ) ^ (-(7 / 10 : ℝ))) := by ring
    _ = C * (n : ℝ) ^ (3 / 10 : ℝ) := by rw [hp]

/-- An actual fixed-temperature saving over exponent 2/3 follows already
from Theorem 1.1; this is an alternative proof of the existential upper
comparison, rather than an assumed OpenAI comparison estimate. -/
theorem strictly_better_than_two_thirds (β : ℝ) (hβ : 1 < β) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      0 ≤ finiteBias n β ∧
        finiteBias n β ≤ C * (n : ℝ) ^ (-(2 / 3 : ℝ) - δ) := by
  obtain ⟨C, hC, hAll⟩ := main_mean_bias β hβ
  refine ⟨1 / 30, C, by norm_num, hC, ?_⟩
  intro n hn
  convert hAll n hn using 1 <;> norm_num

end HexagonPaper
