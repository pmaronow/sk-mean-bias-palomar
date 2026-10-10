module
public import QuantitativePaper.VectorProfilePosteriorScore
public import QuantitativePaper.VectorRecursionUniformTerminalBound

@[expose] public section

/-! A genuine depth-independent bound on the actual affine-profile posterior
score. The terminal offset cancels because the signed Stieltjes direction
has mass zero. The only path-dependent term is the actual retained field norm.
-/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorProfilePosteriorFieldEnvelope (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (z : Fin (N+1)→Field n) : ℝ :=
  ‖fun i : Fin (N+2) => (vectorHistoryFrom s β t (k+2-(N+1)) p x (N+1) z i).2-x‖

theorem vectorProfilePosteriorFieldEnvelope_nonneg (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (z : Fin (N+1)→Field n) :
    0 ≤ vectorProfilePosteriorFieldEnvelope s β t p x N z := norm_nonneg _

theorem vectorProfilePosteriorPotential_sub_terminal_bound
    (s₀ s₁ : RSBScheme k) (β t θ : ℝ) (ht : t ≤ 1)
    (hθ : θ ∈ Icc (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n)
    (N : ℕ) (hN : N+1 ≤ k+2) (z : Fin (N+1)→Field n)
    (i : Option (Fin N)) :
    |vectorProfilePosteriorPotential s₀ s₁ β t p x N z θ i-
        vectorTerminalPotential n β t p x| ≤
      (n:ℝ)*((1-t)*β^2)/2+
        Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z := by
  cases i with
  | none =>
    change |vectorProfileRecursion s₀ s₁ β t θ p (N+1) x-vectorTerminalPotential n β t p x| ≤ _
    rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p]
    exact (abs_vectorRecursion_sub_terminal_uniform _ β t ht p (N+1) hN x).trans
      (le_add_of_nonneg_right (mul_nonneg (Real.sqrt_nonneg _)
        (vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z)))
  | some i =>
    let y := (historyExtended (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z) (i+1)).2
    change |vectorProfileRecursion s₀ s₁ β t θ p (N+1-(i+1)) y-
      vectorTerminalPotential n β t p x| ≤ _
    rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ p]
    have hh := abs_vectorRecursion_sub_initial_terminal_uniform
      (vectorProfileScheme s₀ s₁ θ hθ) β t ht p (N+1-(i+1)) (by omega) x y
    have hn : ‖y-x‖ ≤ vectorProfilePosteriorFieldEnvelope s₀ β t p x N z := by
      exact norm_le_pi_norm
        (fun j : Fin (N+2) => (vectorHistoryFrom s₀ β t (k+2-(N+1)) p x (N+1) z j).2-x)
        (Fin.ofNat (N+2) (i+1))
    exact hh.trans (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)))

theorem norm_vectorProfilePosteriorPotential_deriv_le
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : Fin (N+1)→Field n) (i : Option (Fin N)) :
    ‖deriv (fun φ => vectorProfilePosteriorPotential s₀ s₁ β t p x N z φ i) θ‖ ≤
      (n:ℝ)*((1-t)*β^2)/2 := by
  cases i with
  | none => exact norm_vectorProfileRecursion_profile_deriv_le s₀ s₁ hgrid β t θ ht hθ p (N+1) hN x
  | some i =>
    exact norm_vectorProfileRecursion_profile_deriv_le s₀ s₁ hgrid β t θ ht hθ p _
      (by omega) _

theorem vectorProfilePosteriorLogDensity_deriv_bound_of_centered_potentials
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : (Fin (N+1)→Field n)×Configuration n)
    (V R : ℝ) (hR : 0 ≤ R)
    (hP : ∀i,|vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i-V| ≤ R) :
    |deriv (fun φ => vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ| ≤
      2*R+(n:ℝ)*((1-t)*β^2)/2 := by
  let P := fun i => vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 θ i
  let D := vectorProfilePosteriorDirection s₀ s₁ N
  let a := vectorProfilePosteriorWeight s₀ s₁ N θ
  let B := (n:ℝ)*((1-t)*β^2)/2
  have hB : 0 ≤ B := by dsimp only [B];positivity
  have hdir := vectorProfilePosteriorDirection_total_variation_le s₀ s₁ N hN
  have he : (∑i : Option (Fin N),D i*(P i-V))=∑i : Option (Fin N),D i*P i := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,vectorProfilePosteriorDirection_sum_zero s₀ s₁ N hN,
      zero_mul,sub_zero]
  have hp : |∑i : Option (Fin N),D i*P i| ≤ 2*R := by
    rw [←he]
    calc
      _ ≤ ∑i : Option (Fin N),|D i*(P i-V)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i : Option (Fin N),|D i| * R := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hP i) (abs_nonneg _)
      _ = (∑i : Option (Fin N),|D i|)*R := (Finset.sum_mul ..).symm
      _ ≤ 2*R := mul_le_mul_of_nonneg_right hdir hR
  have hder : |∑i : Option (Fin N),a i*
      deriv (fun φ => vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i) θ| ≤ B := by
    calc
      _ ≤ ∑i : Option (Fin N),|a i*
          deriv (fun φ => vectorProfilePosteriorPotential s₀ s₁ β t p x N z.1 φ i) θ| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i : Option (Fin N),a i*B := Finset.sum_le_sum fun i _ => by
        rw [abs_mul,abs_of_nonneg (vectorProfilePosteriorWeight_nonneg s₀ s₁ N hN θ
          ⟨hθ.1.le,hθ.2.le⟩ i)]
        exact mul_le_mul_of_nonneg_left (norm_vectorProfilePosteriorPotential_deriv_le
          s₀ s₁ hgrid β t θ ht hθ p x N hN z.1 i)
          (vectorProfilePosteriorWeight_nonneg s₀ s₁ N hN θ ⟨hθ.1.le,hθ.2.le⟩ i)
      _ = B := by rw [←Finset.sum_mul,vectorProfilePosteriorWeight_sum s₀ s₁ N hN θ,one_mul]
  rw [(hasDerivAt_vectorProfilePosteriorLogDensity s₀ s₁ β t p x N θ z).deriv,
    abs_neg,Finset.sum_add_distrib]
  exact (abs_add_le _ _).trans (add_le_add hp hder)

theorem vectorProfilePosteriorLogDensity_deriv_bound
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) (N : ℕ) (hN : N+1 ≤ k+2)
    (z : (Fin (N+1)→Field n)×Configuration n) :
    |deriv (fun φ => vectorProfilePosteriorLogDensity s₀ s₁ β t p x N φ z) θ| ≤
      3*((n:ℝ)*((1-t)*β^2)/2)+
        2*Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1 := by
  have hB : 0 ≤ (n:ℝ)*((1-t)*β^2)/2 := by positivity
  have hh := vectorProfilePosteriorLogDensity_deriv_bound_of_centered_potentials s₀ s₁ hgrid
    β t θ ht hθ p x N hN z (vectorTerminalPotential n β t p x)
    ((n:ℝ)*((1-t)*β^2)/2+Real.sqrt (n:ℝ)*vectorProfilePosteriorFieldEnvelope s₀ β t p x N z.1)
    (add_nonneg hB (mul_nonneg (Real.sqrt_nonneg _)
      (vectorProfilePosteriorFieldEnvelope_nonneg s₀ β t p x N z.1)))
    (fun i => vectorProfilePosteriorPotential_sub_terminal_bound s₀ s₁ β t θ ht
      ⟨hθ.1.le,hθ.2.le⟩ p x N hN z.1 i)
  exact hh.trans_eq (by ring)

end QuantitativePaper
