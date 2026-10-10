module
public import OverlapPaper.ReplicaSourceCovariance

@[expose] public section

/-! Literal physical-overlap paths and their grouped covariance/penalty
increments. The grouping hypotheses concern only finite cell geometry. -/
noncomputable section
open Set Real
open scoped BigOperators
namespace OverlapPaper
open FourPapersCommon

def replicaOverlapPath {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ) (q : ℝ) :
    Matrix (Fin d) (Fin d) ℝ := fun l j => min q (D l j)

theorem replicaOverlapPath_zero {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ)
    (hD : ∀ l j, 0 ≤ D l j) : replicaOverlapPath D 0 = 0 := by
  funext l j
  exact min_eq_left (hD l j)

theorem replicaOverlapPath_one {d : ℕ} (D : Matrix (Fin d) (Fin d) ℝ)
    (hD : ∀ l j, D l j ≤ 1) : replicaOverlapPath D 1 = D := by
  funext l j
  exact min_eq_right (hD l j)

theorem replicaOverlapPath_cell_increment {d g : ℕ}
    (D : Matrix (Fin d) (Fin d) ℝ) (q₀ q₁ : ℝ) (hq : q₀ < q₁)
    (groupOf : Fin d → Fin g)
    (hgroup : ∀ l j, groupOf l = groupOf j ↔ q₀ < D l j)
    (hcell : ∀ l j, D l j ≤ q₀ ∨ q₁ ≤ D l j)
    (f : ℝ → ℝ) (l j : Fin d) :
    f (replicaOverlapPath D q₁ l j) - f (replicaOverlapPath D q₀ l j) =
      if groupOf l = groupOf j then f q₁-f q₀ else 0 := by
  rcases hcell l j with hle | hge
  · have hneq : groupOf l ≠ groupOf j := fun hh => (hgroup l j).mp hh |>.not_ge hle
    simp only [replicaOverlapPath, min_eq_right hle,
      min_eq_right (hle.trans hq.le), hneq, ite_false, sub_self]
  · have heq := (hgroup l j).mpr (hq.trans_le hge)
    simp only [replicaOverlapPath, min_eq_left hge,
      min_eq_left (hq.le.trans hge), heq, ite_true]

theorem replicaOverlapPath_covariance_increment {d g : ℕ} (ξ : AdmissibleEvenMixture)
    (D : Matrix (Fin d) (Fin d) ℝ) (q₀ q₁ : ℝ) (hq : q₀ < q₁)
    (groupOf : Fin d → Fin g)
    (hgroup : ∀ l j, groupOf l = groupOf j ↔ q₀ < D l j)
    (hcell : ∀ l j, D l j ≤ q₀ ∨ q₁ ≤ D l j) (l j : Fin d) :
    ξ.first (replicaOverlapPath D q₁ l j)-ξ.first (replicaOverlapPath D q₀ l j) =
      if groupOf l = groupOf j then ξ.first q₁-ξ.first q₀ else 0 :=
  replicaOverlapPath_cell_increment D q₀ q₁ hq groupOf hgroup hcell ξ.first l j

theorem replicaOverlapPath_penalty_increment {d g c : ℕ} (ξ : AdmissibleEvenMixture)
    (D : Matrix (Fin d) (Fin d) ℝ) (q₀ q₁ : ℝ) (hq : q₀ < q₁)
    (groupOf : Fin d → Fin g)
    (hgroup : ∀ l j, groupOf l = groupOf j ↔ q₀ < D l j)
    (hcell : ∀ l j, D l j ≤ q₀ ∨ q₁ ≤ D l j)
    (hfiber : ∀ l, (Finset.univ.filter (fun j => groupOf l=groupOf j)).card = c) :
    replicaTheta ξ (replicaOverlapPath D q₁) - replicaTheta ξ (replicaOverlapPath D q₀) =
      (d : ℝ)*(c : ℝ)*(ξ.correction q₁-ξ.correction q₀) := by
  classical
  unfold replicaTheta
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib,
    replicaOverlapPath_cell_increment D q₀ q₁ hq groupOf hgroup hcell ξ.correction]
  have hh (l : Fin d) : (∑ j : Fin d, if groupOf l=groupOf j then
      ξ.correction q₁-ξ.correction q₀ else 0) =
      (c : ℝ)*(ξ.correction q₁-ξ.correction q₀) := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, hfiber, nsmul_eq_mul] <;> ring
  simp_rw [hh]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem replicaOverlapPath_rescaled_penalty_increment {d g c : ℕ}
    (hc : 0 < c) (ξ : AdmissibleEvenMixture)
    (D : Matrix (Fin d) (Fin d) ℝ) (q₀ q₁ α : ℝ) (hq : q₀ < q₁)
    (groupOf : Fin d → Fin g)
    (hgroup : ∀ l j, groupOf l = groupOf j ↔ q₀ < D l j)
    (hcell : ∀ l j, D l j ≤ q₀ ∨ q₁ ≤ D l j)
    (hfiber : ∀ l, (Finset.univ.filter (fun j => groupOf l=groupOf j)).card = c) :
    (1/2 : ℝ)*(α/(c : ℝ)) *
      (replicaTheta ξ (replicaOverlapPath D q₁)-replicaTheta ξ (replicaOverlapPath D q₀)) =
        (d : ℝ)/2*α*(ξ.correction q₁-ξ.correction q₀) := by
  rw [replicaOverlapPath_penalty_increment ξ D q₀ q₁ hq groupOf hgroup hcell hfiber]
  have hcn : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  field_simp <;> ring

end OverlapPaper
