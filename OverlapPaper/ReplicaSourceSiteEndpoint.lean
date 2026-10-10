module
public import OverlapPaper.ReplicaSourceTerminal
public import OverlapPaper.ReplicaSourceFiniteState

@[expose] public section

/-! Literal site tensorization of the unrestricted replica terminal partition,
and the genuine constrained-to-unrestricted endpoint comparison. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set
open SpinGlass.AT FourPapersCommon
open scoped BigOperators
namespace OverlapPaper

def replicaSiteEnergy {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (x : Fin n → Fin d → ℝ) (σ : ReplicaConfiguration n d) : ℝ :=
  ∑ i : Fin n, ((∑ l : Fin d, (h + x i l) * spin (σ l i)) +
    θ * replicaSpinProduct J (fun l => σ l i))

def replicaSitePartition {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (x : Fin n → Fin d → ℝ) : ℝ :=
  ∑ σ : ReplicaConfiguration n d, Real.exp (replicaSiteEnergy h θ J x σ)

theorem replicaSitePartition_pos {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (x : Fin n → Fin d → ℝ) : 0 < replicaSitePartition h θ J x :=
  Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
    ⟨fun _ _ => false, Finset.mem_univ _, Real.exp_pos _⟩

theorem replicaSitePartition_factor {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (x : Fin n → Fin d → ℝ) :
    replicaSitePartition h θ J x =
      ∏ i : Fin n, ∑ ε : Configuration d,
        Real.exp ((∑ l : Fin d, (h + x i l) * spin (ε l)) + θ * replicaSpinProduct J ε) := by
  classical
  let f : Fin n → Configuration d → ℝ := fun i ε =>
    Real.exp ((∑ l : Fin d, (h + x i l) * spin (ε l)) + θ * replicaSpinProduct J ε)
  have H := (Equiv.piComm (fun _ : Fin d => fun _ : Fin n => Bool)).sum_comp
    (fun σ : Fin n → Configuration d => ∏ i : Fin n, f i (σ i))
  calc
    replicaSitePartition h θ J x = ∑ σ : ReplicaConfiguration n d,
      ∏ i : Fin n, f i (fun l => σ l i) := by
        simp only [replicaSitePartition, replicaSiteEnergy, Real.exp_sum, f]
    _ = ∑ σ : Fin n → Configuration d, ∏ i : Fin n, f i (σ i) := H
    _ = ∏ i : Fin n, ∑ ε : Configuration d, f i ε := by
      simpa only [Fintype.piFinset_univ] using Finset.sum_prod_piFinset Finset.univ f

theorem replicaSiteLogPartition_eq {n d : ℕ} (h θ : ℝ) (J : Finset (Fin d))
    (x : Fin n → Fin d → ℝ) :
    Real.log (replicaSitePartition h θ J x) =
      ∑ i : Fin n, replicaSourceTerminal J θ (fun l => h + x i l) := by
  rw [replicaSitePartition_factor, Real.log_prod]
  · rfl
  · intro i _
    exact (Finset.sum_pos' (fun _ _ => (Real.exp_pos _).le)
      ⟨fun _ => false, Finset.mem_univ _, Real.exp_pos _⟩).ne'

theorem constrained_replicaSiteLogPartition_le {n d : ℕ}
    (h θ : ℝ) (J : Finset (Fin d)) (D : Matrix (Fin d) (Fin d) ℝ) (η : ℝ)
    (x : Fin n → Fin d → ℝ) (hs : (replicaOverlapShell n d D η).Nonempty) :
    Real.log (∑ σ ∈ replicaOverlapShell n d D η, Real.exp (replicaSiteEnergy h θ J x σ)) ≤
      ∑ i : Fin n, replicaSourceTerminal J θ (fun l => h + x i l) := by
  rw [← replicaSiteLogPartition_eq]
  apply Real.log_le_log
  · exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hs
  · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => (Real.exp_pos _).le)

end OverlapPaper
