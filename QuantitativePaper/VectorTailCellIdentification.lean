module
public import QuantitativePaper.VectorTailTimeBounds
public import QuantitativePaper.VectorFiniteCellContinuity

@[expose] public section

/-! The actual restarted finite tail agrees with the genuine single-cell
Cole--Hopf solution throughout every closed profile cell. -/
noncomputable section
open Set
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem vectorTailRecursion_prefix_of_le {n k : ℕ} (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2)
    (hq : q ≤ s.q (k+2-j)) :
    vectorTailRecursion s β t q p j=vectorRecursion s β t p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hlow : q ≤ s.q (k+1-j) := by simpa only [show k+2-(j+1)=k+1-j by omega] using hq
    have hhigh : q ≤ s.q (k+2-j) := hlow.trans (s.q_mono' _ (by omega) _ (by omega))
    rw [vectorTailRecursion,vectorRecursion,ih (by omega) hhigh,
      max_eq_right hhigh,max_eq_right hlow]

theorem vectorTailRecursion_constant_suffix {n k : ℕ} (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) (J : ℕ) (hJ : J ≤ k+2)
    (hq : s.q (k+2-J) ≤ q) {j : ℕ} (hJj : J ≤ j) (hj : j ≤ k+2) :
    vectorTailRecursion s β t q p j=vectorTailRecursion s β t q p J := by
  induction j with
  | zero =>
    have he : J=0 := by omega
    subst J
    rfl
  | succ j ih =>
    by_cases he : J=j+1
    · rw [he]
    · have hJj' : J ≤ j := by omega
      have hhigh : s.q (k+2-j) ≤ q :=
        (s.q_mono' (k+2-J) (by omega) (k+2-j) (by omega)).trans hq
      have hlow : s.q (k+1-j) ≤ q :=
        (s.q_mono' (k+2-j) (by omega) (k+1-j) (by omega)).trans hhigh
      funext x
      rw [vectorTailRecursion,max_eq_left hhigh,max_eq_left hlow]
      simp only [sub_self,mul_zero,vectorColeHopfStep_zero_variance]
      exact congrFun (ih hJj' (by omega)) x

theorem vectorTailRecursion_eq_finiteCell {n k : ℕ} (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) (i : ℕ) (hi : i ≤ k+1)
    (hq : q∈Icc (s.q i) (s.q (i+1))) :
    vectorTailRecursion s β t q p (k+2)=vectorFiniteCellPotential s β t p i q := by
  rw [vectorTailRecursion_constant_suffix s β t q p (k+2-i) (by omega)
    (by simpa only [show k+2-(k+2-i)=i by omega] using hq.1) (by omega) le_rfl]
  rw [show k+2-i=(k+1-i)+1 by omega,vectorTailRecursion]
  have hi0 : k+1-(k+1-i)=i := by omega
  have hi1 : k+2-(k+1-i)=i+1 := by omega
  rw [hi0,hi1,max_eq_left hq.1,max_eq_right hq.2,
    vectorTailRecursion_prefix_of_le s β t q p (by omega)
      (by simpa only [hi1] using hq.2)]
  unfold vectorFiniteCellPotential
  congr 1
  ring

end QuantitativePaper
