module
public import OverlapPaper.ReplicaSourceGroupCovariance

@[expose] public section

/-! Exact standard-Gaussian spectral traces of the actual source disorder and
site/group fields. These are the coefficients in the genuine Guerra trace. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon

theorem source_stdGaussian_covariance_trace {I : Type*} [Fintype I] [DecidableEq I]
    (L M : EuclideanSpace ℝ I →L[ℝ] ℝ) :
    cov[L, M; stdGaussian (EuclideanSpace ℝ I)] =
      ∑ i : I, L (EuclideanSpace.single i 1) * M (EuclideanSpace.single i 1) := by
  let v := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm L
  let w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ I)).symm M
  have hc := covariance_inner_stdGaussian v w
  have hv (z : EuclideanSpace ℝ I) : inner ℝ v z = L z :=
    InnerProductSpace.toDual_symm_apply
  have hw (z : EuclideanSpace ℝ I) : inner ℝ w z = M z :=
    InnerProductSpace.toDual_symm_apply
  rw [show (fun z => inner ℝ v z) = L from funext hv,
    show (fun z => inner ℝ w z) = M from funext hw] at hc
  have hs := (EuclideanSpace.basisFun I ℝ).sum_inner_mul_inner v w
  refine hc.trans (hs.symm.trans ?_)
  apply Finset.sum_congr rfl
  intro i _
  have hwi : inner ℝ ((EuclideanSpace.basisFun I ℝ) i) w =
      M ((EuclideanSpace.basisFun I ℝ) i) :=
    (real_inner_comm w ((EuclideanSpace.basisFun I ℝ) i)).trans (hw _)
  rw [hv, hwi]
  simp only [EuclideanSpace.basisFun_apply]

theorem covariance_sourceReplicaGaussianCoefficient {n d : ℕ}
    (ξ : AdmissibleEvenMixture) (σ τ : ReplicaConfiguration n d) :
    cov[sourceReplicaGaussianCoefficient ξ σ, sourceReplicaGaussianCoefficient ξ τ;
      stdGaussian (Disorder n)] = (n : ℝ) * replicaCovariance ξ σ τ := by
  have H := (hasLaw_sourceGaussianRealization ξ n).covariance_fun_comp
    (f := fun z => ∑ l : Fin d, hamiltonian z (σ l))
    (g := fun z => ∑ j : Fin d, hamiltonian z (τ j))
    (by unfold hamiltonian; fun_prop) (by unfold hamiltonian; fun_prop)
  rw [covariance_replicaHamiltonian] at H
  simpa only [Function.comp_def, hamiltonian, ← sourceReplicaGaussianCoefficient_apply] using H

theorem replicaSourceStateGaussianCLM_spectral_covariance {n d : ℕ}
    (ξ : AdmissibleEvenMixture) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (σ τ : ReplicaSourceState n d D η) :
    (∑ i : Configuration n,
      replicaSourceStateGaussianCLM ξ n d D η (EuclideanSpace.single i 1) σ *
      replicaSourceStateGaussianCLM ξ n d D η (EuclideanSpace.single i 1) τ) =
        (n : ℝ) * replicaCovariance ξ σ.1 τ.1 := by
  simp_rw [replicaSourceStateGaussianCLM_apply]
  rw [← source_stdGaussian_covariance_trace, covariance_sourceReplicaGaussianCoefficient]

theorem replicaGroupFieldCLM_spectral_covariance {n d g : ℕ}
    (D : Matrix (Fin d) (Fin d) ℝ) (η v : ℝ) (hv : 0 ≤ v)
    (groupOf : Fin d → Fin g) (σ τ : ReplicaSourceState n d D η) :
    (∑ i : Fin n × Fin g,
      replicaGroupFieldCLM D η v groupOf (EuclideanSpace.single i 1) σ *
      replicaGroupFieldCLM D η v groupOf (EuclideanSpace.single i 1) τ) =
        (n : ℝ) * replicaFieldCovariance
          (fun l j => if groupOf l = groupOf j then v else 0) σ.1 τ.1 := by
  simp_rw [replicaGroupFieldCLM_apply]
  rw [← source_stdGaussian_covariance_trace, replicaGroupFieldCoordinate_covariance v hv]

end OverlapPaper
