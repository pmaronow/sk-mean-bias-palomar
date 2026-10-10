module
public import QuantitativePaper.LocalJetBounds

@[expose] public section

/-! Actual logarithmic jets inherit exponential growth from positive averaged
jets and a genuine exponential lower bound. Only analytic function bounds are
inputs; no derivative of the logarithm is supplied. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 650000

theorem log_iteratedFDeriv_exponential_bound {N : ℕ} (f : E→ℝ) (U : Set E)
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (C R c D : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : 0 < c) (hD : 0 ≤ D)
    (hupper : ∀ j,j ≤ N → ∀ x ∈ U,‖iteratedFDeriv ℝ j f x‖ ≤ C*Real.exp (R*‖x‖))
    (hlower : ∀ x ∈ U,c*Real.exp (-D*‖x‖) ≤ f x) :
    ∀ j,1 ≤ j → j ≤ N → ∃ A S : ℝ,0 ≤ A ∧ 0 ≤ S ∧
      ∀ x ∈ U,‖iteratedFDeriv ℝ j (fun y=>Real.log (f y)) x‖ ≤ A*Real.exp (S*‖x‖) := by
  let M := max 1 (C/c)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hCM : C ≤ M*c := by
    exact (div_le_iff₀ hc).mp (le_max_right _ _)
  have hpos (x : E) (hx : x ∈ U) : 0 < f x :=
    (mul_pos hc (Real.exp_pos _)).trans_le (hlower x hx)
  intro j hj0 hj
  let A := (j.factorial:ℝ)*logJetCoefficient j*M^j
  let S := (j:ℝ)*(R+D)
  refine ⟨A,S,mul_nonneg (mul_nonneg (by positivity) (logJetCoefficient_nonneg j))
    (pow_nonneg hM0 _),mul_nonneg (by positivity) (add_nonneg hR hD),?_⟩
  intro x hx
  let K := M*Real.exp ((R+D)*‖x‖)
  have hK : 1 ≤ K := by
    exact one_le_mul_of_one_le_of_one_le hM (Real.one_le_exp (mul_nonneg (add_nonneg hR hD) (norm_nonneg _)))
  have hrelative (i : ℕ) (hi : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ i f x‖ ≤ K^i*f x := by
    have hbase : C*Real.exp (R*‖x‖) ≤ K*f x := by
      calc
        C*Real.exp (R*‖x‖) ≤ M*c*Real.exp (R*‖x‖) :=
          mul_le_mul_of_nonneg_right hCM (Real.exp_pos _).le
        _ = K*(c*Real.exp (-D*‖x‖)) := by
          dsimp only [K]
          rw [show (R+D)*‖x‖=R*‖x‖+D*‖x‖ by ring,Real.exp_add,
            show -D*‖x‖=-(D*‖x‖) by ring,Real.exp_neg]
          field_simp
        _ ≤ K*f x := mul_le_mul_of_nonneg_left (hlower x hx) (zero_le_one.trans hK)
    have hpow : K ≤ K^i := by
      simpa using pow_le_pow_right₀ hK hi
    exact (hupper i (hij.trans hj) x hx).trans (hbase.trans
      (mul_le_mul_of_nonneg_right hpow (hpos x hx).le))
  have hh := norm_iteratedFDeriv_log_le_of_relative_on_open f U hU hf hpos hj0 hj K x hx hrelative
  refine hh.trans_eq ?_
  dsimp only [A,S,K]
  rw [mul_pow,←Real.exp_nat_mul]
  rw [show (j:ℝ)*((R+D)*‖x‖)=(j:ℝ)*(R+D)*‖x‖ by ring]
  ring

end QuantitativePaper
