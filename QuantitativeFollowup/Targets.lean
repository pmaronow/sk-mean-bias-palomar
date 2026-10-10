module
public import QuantitativePaper.Model
public import Paper.ParisiPDEFormula

@[expose] public section

/-! Literal main-result targets of the quantitative follow-up. These are
proposition definitions, not proofs. Every random observable and law is
the actual triangular finite SK model and every scalar value is the
actual all-measure Parisi variational value. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativeFollowup

def parisiLimit (β : ℝ) : ℝ := Paper.parisiPDEValue β 0

def finiteBias (n : ℕ) (β : ℝ) : ℝ :=
  parisiLimit β - QuantitativePaper.pressure n β

/-- Theorem 1.1, with fixed-temperature constants and every N≥2. -/
def BiasTarget : Prop :=
  ∀ β : ℝ, 1 < β → ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 2 ≤ n →
    0 ≤ finiteBias n β ∧ finiteBias n β ≤ C*(n:ℝ)^(-(7/10:ℝ))

/-- Theorem 1.2. The upper variance bound holds for every N≥2; the
lower bounds and the complete two-sided tail window hold eventually. -/
def FluctuationTarget : Prop :=
  ∀ β : ℝ, 1 < β → ∃ c C A xβ : ℝ,
    0 < c ∧ 0 < C ∧ 0 < A ∧ 0 < xβ ∧ ∃ N₀ : ℕ,
      (∀ n : ℕ, 2 ≤ n → QuantitativePaper.freeEnergyVariance n β ≤
        C*(n:ℝ)^((11/25:ℝ))) ∧
      (∀ n : ℕ, N₀ ≤ n →
        c*(n:ℝ)^((7/25:ℝ)) ≤ QuantitativePaper.freeEnergyVariance n β ∧
        c*(n:ℝ)^(-(9/10:ℝ)) ≤ finiteBias n β ∧
        ∀ x : ℝ, A*(n:ℝ)^(-(7/10:ℝ)) ≤ x → x ≤ xβ →
          Real.exp (-C*(n:ℝ)*x^((6/5:ℝ))) ≤
            (QuantitativePaper.couplingLaw n
              {g | (n:ℝ)*(parisiLimit β+x) ≤ QuantitativePaper.logPartition n β g}).toReal ∧
          (QuantitativePaper.couplingLaw n
              {g | (n:ℝ)*(parisiLimit β+x) ≤ QuantitativePaper.logPartition n β g}).toReal ≤
            Real.exp (-c*(n:ℝ)*x^((6/5:ℝ))))

end QuantitativeFollowup
