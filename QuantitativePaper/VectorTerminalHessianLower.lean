module
public import QuantitativePaper.VectorFiniteHessianStrict
public import QuantitativePaper.VectorExponentialLocalization

@[expose] public section

/-! Explicit exponential lower bounds for genuine finite Gibbs weights and
the terminal field Hessian. The dimension factor is allowed to depend on N;
the bound supplies localization rather than a sharp response estimate. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators InnerProductSpace
namespace QuantitativePaper
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128

theorem terminalWeight_lower_of_abs_bound {n : ℕ} (E : Configuration n→ℝ)
    (L : ℝ) (hL : ∀σ,|E σ|≤L) (σ : Configuration n) :
    Real.exp (-2*L)/(Fintype.card (Configuration n) : ℝ) ≤ terminalWeight E σ := by
  classical
  have hcard : 0 < (Fintype.card (Configuration n) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hP : terminalPartition E ≤ (Fintype.card (Configuration n) : ℝ)*Real.exp L := by
    unfold terminalPartition
    calc
      _ ≤ ∑ _σ : Configuration n,Real.exp L := Finset.sum_le_sum fun τ _ =>
        Real.exp_le_exp.mpr ((le_abs_self _).trans (hL τ))
      _ = _ := by simp
  unfold terminalWeight
  apply (le_div_iff₀ (terminalPartition_pos E)).mpr
  calc
    _ ≤ (Real.exp (-2*L)/(Fintype.card (Configuration n) : ℝ))*
        ((Fintype.card (Configuration n) : ℝ)*Real.exp L) :=
      mul_le_mul_of_nonneg_left hP (by positivity)
    _ = Real.exp (-2*L)*Real.exp L := by field_simp
    _ = Real.exp (-L) := by rw [←Real.exp_add];congr 1;ring
    _ ≤ Real.exp (E σ) := Real.exp_le_exp.mpr (by
      have hh := neg_le_abs (E σ)
      linarith [hL σ])

theorem terminalCovariance_centered_term_le {n : ℕ} (E b : Configuration n→ℝ)
    (σ : Configuration n) :
    terminalWeight E σ*(b σ-terminalMean E b)^2 ≤ terminalCovariance E b b := by
  classical
  rw [terminalCovariance_centered]
  change terminalWeight E σ*(b σ-terminalMean E b)^2 ≤
    ∑ τ,terminalWeight E τ*((b τ-terminalMean E b)*(b τ-terminalMean E b))
  simpa only [pow_two] using Finset.single_le_sum
    (fun τ _=>mul_nonneg (terminalWeight_pos E τ).le
      (mul_self_nonneg (b τ-terminalMean E b))) (Finset.mem_univ σ)

theorem terminalCovariance_fieldDot_lower {n : ℕ} (hn : 0<n) (E : Configuration n→ℝ)
    (L : ℝ) (hL : ∀σ,|E σ|≤L) (w : Field n) :
    (Real.exp (-2*L)/((n : ℝ)*(Fintype.card (Configuration n) : ℝ)))*‖w‖^2 ≤
      terminalCovariance E (fieldDot w) (fieldDot w) := by
  classical
  let c := Real.exp (-2*L)/(Fintype.card (Configuration n) : ℝ)
  have hc : 0≤c := by dsimp [c];positivity
  let V := terminalCovariance E (fieldDot w) (fieldDot w)
  have hi (i : Fin n) : c*(w i)^2 ≤ V := by
    let σ : Configuration n:=fun _=>true
    let τ : Configuration n:=Function.update σ i false
    have hd : fieldDot w τ-fieldDot w σ= -2*w i := by
      unfold fieldDot
      rw [←Finset.sum_sub_distrib]
      have he (j : Fin n) : w j*Paper.spinSign (τ j)-w j*Paper.spinSign (σ j)=
          if j=i then -2*w i else 0:=by
        by_cases hj:j=i
        · subst j;simp [τ,σ,Paper.spinSign];ring
        · simp [τ,σ,Function.update_apply,hj,Paper.spinSign]
      simp_rw [he]
      simp
    have he (v : Configuration n) : c*(fieldDot w v-terminalMean E (fieldDot w))^2 ≤ V :=
      (mul_le_mul_of_nonneg_right (terminalWeight_lower_of_abs_bound E L hL v) (sq_nonneg _)).trans
        (terminalCovariance_centered_term_le E (fieldDot w) v)
    have hp := mul_nonneg hc (sq_nonneg ((fieldDot w σ-terminalMean E (fieldDot w))+
      (fieldDot w τ-terminalMean E (fieldDot w))))
    have hτ:=he τ
    have heq : fieldDot w τ=fieldDot w σ-2*w i:=by linarith only [hd]
    rw [heq] at hτ hp
    nlinarith only [he σ,hτ,hp]
  have hh := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n)))=>hi i)
  have hsum : c*‖w‖^2 ≤ (n : ℝ)*V := by
    simpa only [←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hh
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  calc
    _ = (c*‖w‖^2)/(n : ℝ) := by dsimp [c];field_simp
    _ ≤ V := (div_le_iff₀ hn').mpr (by simpa only [mul_comm] using hsum)

theorem vectorTerminalExponent_abs_bound {n : ℕ} (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (σ : Configuration n) :
    |vectorTerminalExponent n β t p x σ| ≤
      vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖ := by
  unfold vectorTerminalExponent
  apply (abs_add_le _ _).trans
  apply add_le_add _ (abs_fieldDot x σ)
  rw [abs_mul,abs_mul,abs_of_nonneg (Real.sqrt_nonneg t)]
  exact mul_le_mul_of_nonneg_left
    ((abs_add_le _ _).trans (add_le_add (abs_energy_le_envelope n p.1 σ) le_rfl)) (by positivity)

theorem vectorTerminalHessian_exponential_lower {n k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (hn : 0<n) (β t : ℝ)
    (p : Couplings n×ℝ) (x w : Field n) :
    (Real.exp (-2*(vectorDisorderEnvelope n β t p+Real.sqrt (n : ℝ)*‖x‖))/
      ((n : ℝ)*(Fintype.card (Configuration n) : ℝ)))*‖w‖^2 ≤
      inner ℝ w (vectorFieldHessian s β t p 0 x w) := by
  rw [vectorFieldHessian_quadratic_eq_secondResponse]
  simpa [vectorObservableSecondResponse,terminalTilt] using
    terminalCovariance_fieldDot_lower hn _ _ (vectorTerminalExponent_abs_bound β t p x) w

end QuantitativePaper
