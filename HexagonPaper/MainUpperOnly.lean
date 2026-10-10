module
public import HexagonPaper.Main

@[expose] public section

/-! The literal one-sided main conclusion of the revised manuscript. -/

noncomputable section
open QuantitativeFollowup QuantitativePaper

namespace HexagonPaper

/-- Theorem 1.1's upper bound, projected from the stronger proved mean-bias bound. -/
theorem main_mean_bias_upper (β : ℝ) (hβ : 1 < β) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
      finiteBias n β ≤ C * (n : ℝ) ^ (-(7 / 10 : ℝ)) := by
  obtain ⟨C, hC, hAll⟩ := main_mean_bias β hβ
  exact ⟨C, hC, fun n hn => (hAll n hn).2⟩

end HexagonPaper
