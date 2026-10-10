module
public import QuantitativePaper.VectorEnergyRegularity

@[expose] public section

/-! Strict finite-temperature terminal magnetization bounds. Every spin has
strictly positive actual Gibbs weight, so the endpoint overlap is below one. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace QuantitativePaper

theorem terminalMean_lt_of_bound {n : ℕ} (E b : Configuration n → ℝ) (R : ℝ)
    (hb : ∀σ,b σ ≤ R) (hs : ∃σ,b σ < R) : terminalMean E b < R := by
  classical
  obtain ⟨σ,hσ⟩ := hs
  have h : (∑τ,terminalWeight E τ*b τ)<∑τ,terminalWeight E τ*R := by
    apply Finset.sum_lt_sum
    · intro τ _
      exact mul_le_mul_of_nonneg_left (hb τ) (terminalWeight_pos E τ).le
    · exact ⟨σ,Finset.mem_univ σ,mul_lt_mul_of_pos_left hσ (terminalWeight_pos E σ)⟩
  simpa only [terminalMean,←Finset.sum_mul,terminalWeight_sum,one_mul] using h

theorem terminalMean_spin_abs_lt_one {n : ℕ} (E : Configuration n → ℝ) (i : Fin n) :
    |terminalMean E (fun σ => Paper.spinSign (σ i))|<1 := by
  have hU : terminalMean E (fun σ => Paper.spinSign (σ i))<1 :=
    terminalMean_lt_of_bound E _ 1 (fun σ => by cases σ i <;> norm_num [Paper.spinSign])
      ⟨fun _ => false,by norm_num [Paper.spinSign]⟩
  have hL : terminalMean E (fun σ => -Paper.spinSign (σ i))<1 :=
    terminalMean_lt_of_bound E _ 1 (fun σ => by cases σ i <;> norm_num [Paper.spinSign])
      ⟨fun _ => true,by norm_num [Paper.spinSign]⟩
  have he : terminalMean E (fun σ => -Paper.spinSign (σ i))=
      -terminalMean E (fun σ => Paper.spinSign (σ i)) := by
    simpa only [neg_one_mul] using terminalMean_const_mul E (fun σ => Paper.spinSign (σ i)) (-1)
  rw [he] at hL
  exact abs_lt.mpr ⟨by linarith,hU⟩

theorem vectorTerminalMagnetization_component_abs_lt_one (n : ℕ) (β t : ℝ)
    (p : Couplings n × ℝ) (x : Field n) (i : Fin n) :
    |vectorTerminalMagnetization n β t p x i|<1 :=
  terminalMean_spin_abs_lt_one _ i

theorem vectorTerminalMagnetization_norm_sq_lt {n : ℕ} (hn : 0 < n)
    (β t : ℝ) (p : Couplings n × ℝ) (x : Field n) :
    ‖WithLp.toLp 2 (vectorTerminalMagnetization n β t p x)‖^2<(n : ℝ) := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ < ∑_ : Fin n,(1 : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro i _
        have h := abs_lt.mp (vectorTerminalMagnetization_component_abs_lt_one n β t p x i)
        nlinarith
    _ = _ := by simp

end QuantitativePaper
