module
public import OverlapPaper.ReplicaSourceGaussian
public import FourPapersCommon.MixtureCoercivity

@[expose] public section

/-! The exact d-replica disorder covariance, its physical-overlap tangent
completion, and the shell diagonal error. No overlap is replaced by a clock. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon

def replicaCovariance {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (σ τ : ReplicaConfiguration n d) : ℝ :=
  ∑ l : Fin d, ∑ j : Fin d, ξ.value (overlap (σ l) (τ j))

def replicaFieldCovariance {n d : ℕ} (B : Matrix (Fin d) (Fin d) ℝ)
    (σ τ : ReplicaConfiguration n d) : ℝ :=
  ∑ l : Fin d, ∑ j : Fin d, B l j * overlap (σ l) (τ j)

def replicaTangentDefect {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (B : Matrix (Fin d) (Fin d) ℝ) (σ τ : ReplicaConfiguration n d) : ℝ :=
  ∑ l : Fin d, ∑ j : Fin d, ξ.tangentRemainder (overlap (σ l) (τ j)) (B l j)

def replicaTheta {d : ℕ} (ξ : AdmissibleEvenMixture)
    (B : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ l : Fin d, ∑ j : Fin d, ξ.correction (B l j)

theorem covariance_replicaHamiltonian {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (σ τ : ReplicaConfiguration n d) :
    cov[fun g : Disorder n => ∑ l : Fin d, hamiltonian g (σ l),
      fun g => ∑ j : Fin d, hamiltonian g (τ j); disorderLaw ξ n] =
        (n : ℝ) * replicaCovariance ξ σ τ := by
  change cov[fun g : Disorder n => ∑ l : Fin d, (EuclideanSpace.proj (σ l)) g,
    fun g => ∑ j : Fin d, (EuclideanSpace.proj (τ j)) g; disorderLaw ξ n] = _
  rw [covariance_fun_sum_fun_sum
    (fun l => IsGaussian.memLp_dual (disorderLaw ξ n) (EuclideanSpace.proj (σ l)) 2 (by simp))
    (fun j => IsGaussian.memLp_dual (disorderLaw ξ n) (EuclideanSpace.proj (τ j)) 2 (by simp))]
  change (∑ l : Fin d, ∑ j : Fin d, cov[fun g : Disorder n => hamiltonian g (σ l),
    fun g => hamiltonian g (τ j); disorderLaw ξ n]) = _
  simp_rw [covariance_hamiltonian]
  simp only [replicaCovariance, Finset.mul_sum]

theorem replica_covariance_tangent_completion {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (B : Matrix (Fin d) (Fin d) ℝ) (σ τ : ReplicaConfiguration n d) :
    replicaCovariance ξ σ τ - replicaFieldCovariance (fun l j => ξ.first (B l j)) σ τ =
      replicaTangentDefect ξ B σ τ - replicaTheta ξ B := by
  have H : replicaTangentDefect ξ B σ τ =
      replicaCovariance ξ σ τ - replicaFieldCovariance (fun l j => ξ.first (B l j)) σ τ +
        replicaTheta ξ B := by
    simp only [replicaCovariance, replicaFieldCovariance, replicaTangentDefect,
      replicaTheta, AdmissibleEvenMixture.tangentRemainder_eq,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_comm]
  rw [H]
  ring

theorem replicaTangentDefect_nonneg {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (B : Matrix (Fin d) (Fin d) ℝ) (hB : ∀ l j, B l j ∈ Icc (-1 : ℝ) 1)
    (σ τ : ReplicaConfiguration n d) : 0 ≤ replicaTangentDefect ξ B σ τ := by
  apply Finset.sum_nonneg
  intro l _
  apply Finset.sum_nonneg
  intro j _
  exact ξ.tangentRemainder_nonneg (overlap_mem_unit _ _) (hB l j)

theorem replicaShell_overlap_close {n d : ℕ} (hn : 0 < n)
    (D : Matrix (Fin d) (Fin d) ℝ) (hDsymm : ∀ l j, D l j = D j l)
    (hDdiag : ∀ l, D l l = 1) (η : ℝ) (hη : 0 ≤ η)
    (σ : ReplicaConfiguration n d) (hσ : σ ∈ replicaOverlapShell n d D η)
    (l j : Fin d) : |overlap (σ l) (σ j) - D l j| ≤ η := by
  have H := (mem_replicaOverlapShell D η σ).mp hσ
  rcases lt_trichotomy l j with hlt | rfl | hgt
  · exact (H l j hlt).le
  · simp only [overlap_self hn, hDdiag, sub_self, abs_zero]
    exact hη
  · rw [overlap_symm, hDsymm]
    exact (H j l hgt).le

theorem replicaTangentDefect_shell_diagonal_le {n d : ℕ} (hn : 0 < n)
    (ξ : AdmissibleEvenMixture) (D : Matrix (Fin d) (Fin d) ℝ)
    (hD : ∀ l j, D l j ∈ Icc (-1 : ℝ) 1)
    (hDsymm : ∀ l j, D l j = D j l) (hDdiag : ∀ l, D l l = 1)
    (η : ℝ) (hη : 0 ≤ η) (σ : ReplicaConfiguration n d)
    (hσ : σ ∈ replicaOverlapShell n d D η) :
    replicaTangentDefect ξ D σ σ ≤ (d : ℝ) ^ 2 * ξ.second 1 * η ^ 2 := by
  have hs (l j : Fin d) :
      ξ.tangentRemainder (overlap (σ l) (σ j)) (D l j) ≤ ξ.second 1 * η ^ 2 := by
    refine (ξ.tangentRemainder_quadratic_upper (overlap_mem_unit _ _) (hD l j)).trans ?_
    apply mul_le_mul_of_nonneg_left _ (ξ.second_nonneg 1)
    have hh := replicaShell_overlap_close hn D hDsymm hDdiag η hη σ hσ l j
    nlinarith [sq_nonneg (overlap (σ l) (σ j) - D l j), abs_nonneg (overlap (σ l) (σ j) - D l j), sq_abs (overlap (σ l) (σ j) - D l j)]
  calc
    _ ≤ ∑ _l : Fin d, ∑ _j : Fin d, ξ.second 1 * η ^ 2 :=
      Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun j _ => hs l j))
    _ = _ := by simp; ring

end OverlapPaper
