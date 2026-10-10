module
public import QuantitativePaper.LocalJetBounds
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section

/-! Products of actual local jets with a bounded parameter factor preserve
an exponential envelope. Zeroth jets are included explicitly. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

theorem norm_iteratedFDeriv_mul_le_of_power_envelope {N j : ℕ} (f g : E → ℝ)
    (U : Set E) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) (hg : ContDiffOn ℝ N g U)
    (hj0 : 1 ≤ j) (hj : j ≤ N) (x : E) (hx : x ∈ U) (M P : ℝ)
    (hM : 1 ≤ M) (hP : 1 ≤ P)
    (hfj : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i f x‖ ≤ P^(i+1))
    (hgj : ∀ i, i ≤ j → ‖iteratedFDeriv ℝ i g x‖ ≤ M) :
    ‖iteratedFDeriv ℝ j (fun y => g y*f y) x‖ ≤ (2*M*P^2)^j := by
  have hM0 := zero_le_one.trans hM
  have hP0 := zero_le_one.trans hP
  have hn := norm_iteratedFDeriv_mul_le_on_open g f U hU hg hf hj x hx
  have hs : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*
      ‖iteratedFDeriv ℝ i g x‖*‖iteratedFDeriv ℝ (j-i) f x‖) ≤
      (2:ℝ)^j*M*P^(j+1) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)*M*P^(j+1) := by
        apply Finset.sum_le_sum
        intro i hi
        have hij : i ≤ j := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
        have hfp := (hfj (j-i) (Nat.sub_le _ _)).trans
          (pow_le_pow_right₀ hP (by omega : j-i+1 ≤ j+1))
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hgj i hij) (by positivity))
          hfp (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have he : (∑ i ∈ Finset.range (j+1), (j.choose i:ℝ)) = (2:ℝ)^j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [he]
  apply hn.trans (hs.trans ?_)
  have hMp : M ≤ M^j := le_self_pow₀ hM (by omega)
  have hPp : P^(j+1) ≤ P^(2*j) := pow_le_pow_right₀ hP (by omega)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hMp (by positivity : 0 ≤ (2:ℝ)^j))
    hPp (by positivity) (by positivity)
  simpa only [mul_pow, pow_mul] using hh

theorem linear_growth_le_exponential (B L r : ℝ) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hr : 0 ≤ r) : B+L*r ≤ (B+L)*Real.exp r := by
  have he := Real.add_one_le_exp r
  have hh := mul_le_mul_of_nonneg_left he (add_nonneg hB hL)
  nlinarith

end QuantitativePaper
