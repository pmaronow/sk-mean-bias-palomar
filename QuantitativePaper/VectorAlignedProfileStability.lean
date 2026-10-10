module
public import QuantitativePaper.VectorMassBounds

@[expose] public section

/-! Genuine finite-profile coefficient stability on a common overlap grid.
Every constant is independent of the recursion depth and the disorder. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

def vectorAlignedProfileError {n k : ℕ} (s r : RSBScheme k) (β t : ℝ) (j : ℕ) : ℝ :=
  ∑l∈Finset.range j,(n : ℝ)*((1-t)*(β^2*(s.q (k+2-l)-s.q (k+1-l))))*
    |s.m (k+1-l)-r.m (k+1-l)|

theorem vectorRecursion_aligned_profile_abs_sub_le {n k : ℕ} (s r : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (hq : ∀i,i ≤ k+2 → s.q i=r.q i)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) :
    |vectorRecursion s β t p j x-vectorRecursion r β t p j x| ≤
      vectorAlignedProfileError (n := n) s r β t j := by
  induction j generalizing x with
  | zero => simp [vectorRecursion,vectorAlignedProfileError]
  | succ j ih =>
    let v := (1-t)*(β^2*(s.q (k+2-j)-s.q (k+1-j)))
    have hv : 0 ≤ v := mul_nonneg (sub_nonneg.mpr ht)
      (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr
        (s.q_mono' (k+2-j) (Nat.sub_le _ _) (k+1-j) (by omega))))
    have hvr : (1-t)*(β^2*(r.q (k+2-j)-r.q (k+1-j)))=v := by
      rw [←hq _ (Nat.sub_le _ _),←hq _ (by omega)]
    simp only [vectorRecursion]
    rw [hvr]
    have hn := abs_vectorColeHopfStep_sub_le (vectorRecursion s β t p j) (vectorRecursion r β t p j)
      _ (vectorRecursion_lipschitz s β t p j) (vectorRecursion_lipschitz r β t p j)
      v (s.m (k+1-j)) (vectorAlignedProfileError (n := n) s r β t j)
      (s.m_nonneg (Nat.sub_le _ _)) ih x
    have hm := vectorColeHopfStep_recursion_mass_abs_sub_le r β t v hv p j x
      (s.m (k+1-j)) (r.m (k+1-j)) (s.m_nonneg (Nat.sub_le _ _)) (r.m_nonneg (Nat.sub_le _ _))
    rw [abs_sub_comm] at hm
    calc
      _ ≤ |vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion s β t p j) x-
          vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion r β t p j) x|+
        |vectorColeHopfStep v (s.m (k+1-j)) (vectorRecursion r β t p j) x-
          vectorColeHopfStep v (r.m (k+1-j)) (vectorRecursion r β t p j) x| := abs_sub_le _ _ _
      _ ≤ vectorAlignedProfileError (n := n) s r β t j+(n : ℝ)*v*|r.m (k+1-j)-s.m (k+1-j)| :=
        add_le_add hn hm
      _ = vectorAlignedProfileError (n := n) s r β t (j+1) := by
        simp only [vectorAlignedProfileError,Finset.sum_range_succ]
        rw [abs_sub_comm]

end QuantitativePaper
