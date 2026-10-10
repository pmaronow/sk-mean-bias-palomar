module
public import QuantitativePaper.ScalarLogThirdDerivative
public import Mathlib.Tactic.IntervalCases

@[expose] public section

/-! Explicit first three exponential scalar jets are controlled by
the literal first three source jets. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
set_option maxHeartbeats 1400000

def scalarExponentialJetBound (a B M R : ℝ) (r : ℕ) : ℝ:=
  match r with
  | 1=>|a| *B
  | 2=>|a| *M+a^2*B^2
  | 3=>|a| *R+3*a^2*B*M+|a| ^3*B^3
  | _=>0

theorem scalarExponentialJetBound_nonneg (a B M R : ℝ)
    (hB : 0≤B) (hM : 0≤M) (hR : 0≤R) (r : ℕ) :
    0≤scalarExponentialJetBound a B M R r := by
  unfold scalarExponentialJetBound
  split <;> positivity

theorem norm_iteratedDeriv_exp_three_jets_le (f : ℝ→ℝ) (a : ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ 3 f U)
    (B M R : ℝ) (hB : 0≤B) (hM : 0≤M) (hR : 0≤R)
    (θ : ℝ) (hθ : θ∈U) (h1 : |deriv f θ|≤B)
    (h2 : |iteratedDeriv 2 f θ|≤M) (h3 : |iteratedDeriv 3 f θ|≤R)
    (r : ℕ) (hr : r∈Finset.Icc 1 3) :
    ‖iteratedDeriv r (fun φ=>Real.exp (a*f φ)) θ‖≤
      scalarExponentialJetBound a B M R r*Real.exp (a*f θ) := by
  have hs1' : |deriv f θ|^2≤B^2:=(sq_le_sq₀ (abs_nonneg _) hB).mpr h1
  have hr' : 1≤r ∧ r≤3:=Finset.mem_Icc.mp hr
  obtain ⟨hrl,hru⟩:=hr'
  interval_cases r
  · have hd:=(((hf θ hθ).contDiffAt (hU.mem_nhds hθ)).differentiableAt
      (by norm_num)).hasDerivAt
    rw [iteratedDeriv_one,((hd.const_mul a).exp).deriv,Real.norm_eq_abs,abs_mul,
      abs_of_pos (Real.exp_pos _),abs_mul]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (abs_nonneg a))
      (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · rw [iteratedDeriv_two_exp_mul_on_open f a U hU (hf.of_le (by norm_num)) hθ,
      Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
    have hb : |a*iteratedDeriv 2 f θ+a^2*(deriv f θ)^2|≤|a| *M+a^2*B^2:=by
      apply (abs_add_le _ _).trans
      simp only [abs_mul,abs_pow,sq_abs]
      exact add_le_add (mul_le_mul_of_nonneg_left h2 (abs_nonneg a))
        (mul_le_mul_of_nonneg_left (by simpa only [sq_abs] using hs1') (sq_nonneg a))
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · rw [iteratedDeriv_three_exp_mul_on_open f a U hU hf hθ,Real.norm_eq_abs,abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hb : |a*iteratedDeriv 3 f θ+3*a^2*deriv f θ*iteratedDeriv 2 f θ+a^3*(deriv f θ)^3|≤
        |a| *R+3*a^2*B*M+|a| ^3*B^3:=by
      apply ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
      simp only [abs_mul,abs_pow,sq_abs,abs_of_pos (by norm_num : (0:ℝ)<3)]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left h3 (abs_nonneg a))
        (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) h2 (abs_nonneg _) (by positivity)))
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) h1 3) (by positivity))
    exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans_eq (mul_comm _ _)

end QuantitativePaper
