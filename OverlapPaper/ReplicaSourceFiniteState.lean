module
public import OverlapPaper.ReplicaSourceCovariance
public import FourPapersCommon.FiniteStateCascadeDefinitions

@[expose] public section

/-! The literal constrained source model as a finite-state log partition.
The Gaussian map sums the original replica Hamiltonians; the deterministic
potential includes every field term and the exact source monomial. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
open SpinGlass.AT FourPapersCommon
open scoped BigOperators
namespace OverlapPaper

abbrev ReplicaSourceState (n d : ℕ) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :=
  ↥(replicaOverlapShell n d D η)

def replicaSourceDisorderField (n d : ℕ) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (g : Disorder n) : FiniteStateField (ReplicaSourceState n d D η) :=
  WithLp.toLp 2 (fun σ => ∑ l : Fin d, g (σ.1 l))

def replicaSourceDisorderCLM (n d : ℕ) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Disorder n →L[ℝ] FiniteStateField (ReplicaSourceState n d D η) :=
  LinearMap.toContinuousLinearMap
    { toFun := replicaSourceDisorderField n d D η
      map_add' := by intro x y; ext σ; simp [replicaSourceDisorderField, Finset.sum_add_distrib]
      map_smul' := by intro c x; ext σ; simp [replicaSourceDisorderField, Finset.mul_sum] }

def replicaSourceStatePotential {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (σ : ReplicaSourceState n d D η) : ℝ :=
  (∑ l : Fin d, h * ∑ i : Fin n, spin (σ.1 l i)) +
    θ * ∑ i : Fin n, replicaSpinProduct J (fun l => σ.1 l i)

def replicaSourceStateGaussianCLM (ξ : AdmissibleEvenMixture) (n d : ℕ)
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Disorder n →L[ℝ] FiniteStateField (ReplicaSourceState n d D η) :=
  (replicaSourceDisorderCLM n d D η).comp (sourceGaussianRealization ξ n)

theorem replicaSourceStatePartition_eq {n d : ℕ} (hn : 0 < n)
    (h θ : ℝ) (J : Finset (Fin d)) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (g : Disorder n) :
    gtStatePartition (replicaSourceStatePotential h θ J D η)
      (replicaSourceDisorderCLM n d D η g) = replicaSourcePartition h θ J D η g := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have he (σ : ReplicaSourceState n d D η) :
      replicaSourceDisorderCLM n d D η g σ + replicaSourceStatePotential h θ J D η σ =
        replicaSourceEnergy h θ J g σ.1 := by
    change (∑ l : Fin d, g (σ.1 l)) + replicaSourceStatePotential h θ J D η σ = _
    simp only [replicaSourceStatePotential, replicaSourceEnergy, replicaSourceAverage,
      totalHamiltonian, hamiltonian, Finset.sum_add_distrib]
    field_simp
    ring

  simp_rw [gtStatePartition, he]
  exact Finset.sum_coe_sort (replicaOverlapShell n d D η)
    (fun σ => Real.exp (replicaSourceEnergy h θ J g σ))

theorem replicaSourceStateLogPartition_eq {n d : ℕ} (hn : 0 < n)
    (h θ : ℝ) (J : Finset (Fin d)) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (g : Disorder n) :
    gtStateLogPartition (replicaSourceStatePotential h θ J D η)
      (replicaSourceDisorderCLM n d D η g) = (n : ℝ) * replicaSourcePressureValue h θ J D η g := by
  rw [gtStateLogPartition, replicaSourceStatePartition_eq hn]
  unfold replicaSourcePressureValue
  field_simp

theorem replicaSourceStateGaussianCLM_apply {n d : ℕ} (ξ : AdmissibleEvenMixture)
    (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) (z : Disorder n)
    (σ : ReplicaSourceState n d D η) :
    replicaSourceStateGaussianCLM ξ n d D η z σ = sourceReplicaGaussianCoefficient ξ σ.1 z := by
  rw [sourceReplicaGaussianCoefficient_apply]
  rfl

end OverlapPaper
