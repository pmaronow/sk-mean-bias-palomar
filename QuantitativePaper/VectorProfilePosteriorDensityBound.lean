module
public import QuantitativePaper.VectorProfilePosteriorScoreBound

@[expose] public section

/-! The literal posterior density has a Gaussian exponential envelope.
The fixed terminal offset cancels exactly from its Stieltjes weights. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem terminalExponent_le_terminalPotential (E : Configuration n→ℝ) (σ : Configuration n) :
    E σ≤terminalPotential E := by
  have he : Real.exp (E σ)≤terminalPartition E :=
    Finset.single_le_sum (fun _ _=>(Real.exp_pos _).le) (Finset.mem_univ σ)
  have hl:=Real.log_le_log (Real.exp_pos (E σ)) he
  simpa only [Real.log_exp,terminalPotential] using hl

theorem vectorTerminalExponent_sub_initial_potential_le (β t : ℝ)
    (p : Couplings n×ℝ) (x y : Field n) (σ : Configuration n) :
    vectorTerminalExponent n β t p y σ-vectorTerminalPotential n β t p x≤
      Real.sqrt (n:ℝ)*‖y-x‖ := by
  have h0:=terminalExponent_le_terminalPotential (vectorTerminalExponent n β t p x) σ
  have hf:vectorTerminalExponent n β t p y σ-vectorTerminalExponent n β t p x σ=
      fieldDot (y-x) σ := by
    simp only [vectorTerminalExponent,add_sub_add_left_eq_sub,fieldDot_sub]
  have hb:= (le_abs_self (fieldDot (y-x) σ)).trans (abs_fieldDot (y-x) σ)
  change vectorTerminalExponent n β t p x σ≤vectorTerminalPotential n β t p x at h0
  rw [←hf] at hb
  linarith

theorem vectorProfilePosteriorLogDensity_upper (s₀ s₁ : RSBScheme k)
    (β t θ : ℝ) (ht : t≤1) (hθ : θ∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1≤k+2)
    (z : (Fin (N+1)→Field n)×Configuration n) :
    vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z≤
      (n:ℝ)*((1-t)*β^2)/2+
        2*Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1 := by
  let V:=vectorTerminalPotential n β t p x
  let R:=(n:ℝ)*((1-t)*β^2)/2+
    Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1
  have hsum : V-R≤∑i : Option (Fin N),vectorProfilePosteriorWeight s₀ s₁ N θ i*
      vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i := by
    calc
      _ = ∑i : Option (Fin N),vectorProfilePosteriorWeight s₀ s₁ N θ i*(V-R) := by
        rw [←Finset.sum_mul,vectorProfilePosteriorWeight_sum s₀ s₁ N hN θ,one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _=>by
        apply mul_le_mul_of_nonneg_left _ (vectorProfilePosteriorWeight_nonneg s₀ s₁ N hN θ hθ i)
        have hb:= (abs_le.mp (vectorProfilePosteriorPotential_sub_terminal_bound s₀ s₁ β t θ ht
          hθ p x N hN z.1 i)).1
        change -R≤vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i-V at hb
        linarith
  let y:=(vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z.1 (Fin.last (N+1))).2
  have hn : ‖y-x‖≤vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1 :=
    norm_le_pi_norm (fun i : Fin (N+2)=>
      (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z.1 i).2-x) (Fin.last (N+1))
  have hterm:vectorTerminalExponent n β t p y z.2-V≤
      Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1 :=
    (vectorTerminalExponent_sub_initial_potential_le β t p x y z.2).trans
      (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))
  unfold vectorProfilePosteriorLogDensity
  dsimp only [V,R,y] at hsum hterm
  linarith

end QuantitativePaper
