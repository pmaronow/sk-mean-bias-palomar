module
public import QuantitativePaper.VectorTailProfileStability
public import QuantitativePaper.VectorVarianceBounds

@[expose] public section

/-! Uniform time-Lipschitz estimates for actual finite restarted tails.
No derivative at an atomic overlap or at zero variance is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem clamped_interval_length_antitone (q r a b : ℝ) (hqr : q ≤ r) (hab : a ≤ b) :
    max r b-max r a ≤ max q b-max q a := by
  simp only [max_def]
  split_ifs <;> linarith

theorem vectorTailRecursion_lipschitz {n k : ℕ} (s : RSBScheme k) (β t q : ℝ)
    (hq : q∈Icc (0 : ℝ) 1) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) :
    LipschitzWith (Real.sqrt (n : ℝ)).toNNReal (vectorTailRecursion s β t q p j) := by
  rw [vectorTailRecursion_eq_clamped s β t q hq p hj]
  exact vectorRecursion_lipschitz _ β t p j

theorem vectorTailRecursion_time_partial_abs_sub_le {n k : ℕ} (s : RSBScheme k)
    (β t q r : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (hr : r∈Icc (0 : ℝ) 1)
    (hqr : q ≤ r) (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) (x : Field n) :
    |vectorTailRecursion s β t q p j x-vectorTailRecursion s β t r p j x| ≤
      (n : ℝ)*((1-t)*β^2)/2*(max r (s.q (k+2-j))-max q (s.q (k+2-j))) := by
  induction j generalizing x with
  | zero => simp [vectorTailRecursion,s.q_top,max_eq_right hr.2,max_eq_right hq.2]
  | succ j ih =>
    let c := (1-t)*β^2
    have hc : 0 ≤ c := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg β)
    let vq := (1-t)*(β^2*(max q (s.q (k+2-j))-max q (s.q (k+1-j))))
    let vr := (1-t)*(β^2*(max r (s.q (k+2-j))-max r (s.q (k+1-j))))
    have hnodes : s.q (k+1-j) ≤ s.q (k+2-j) := s.q_mono' _ (by omega) _ (by omega)
    have hvq : 0 ≤ vq := by
      unfold vq
      exact mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg β)
        (sub_nonneg.mpr (max_le_max le_rfl hnodes)))
    have hvr : 0 ≤ vr := by
      unfold vr
      exact mul_nonneg (sub_nonneg.mpr ht) (mul_nonneg (sq_nonneg β)
        (sub_nonneg.mpr (max_le_max le_rfl hnodes)))
    have hvar : vr ≤ vq := by
      have hh := mul_le_mul_of_nonneg_left (clamped_interval_length_antitone q r _ _ hqr hnodes) hc
      simpa only [c,mul_assoc] using hh
    let R := (n : ℝ)*c/2*(max r (s.q (k+2-j))-max q (s.q (k+2-j)))
    have hinputs : ∀y,|vectorTailRecursion s β t q p j y-vectorTailRecursion s β t r p j y| ≤ R :=
      fun y => ih (by omega) y
    have hsame := abs_vectorColeHopfStep_sub_le _ _ _
      (vectorTailRecursion_lipschitz s β t q hq p (by omega))
      (vectorTailRecursion_lipschitz s β t r hr p (by omega)) vq (s.m (k+1-j)) R
      (s.m_nonneg (by omega)) hinputs x
    have hm : s.m (k+1-j)∈Icc (0 : ℝ) 1 :=
      ⟨s.m_nonneg (by omega),s.m_le_one (by omega)⟩
    have hvary := vectorColeHopfStep_recursion_variance_sub_bounds (vectorClampedScheme s r hr)
      β t p j (s.m (k+1-j)) hm vr vq hvr hvar x
    rw [←vectorTailRecursion_eq_clamped s β t r hr p (by omega)] at hvary
    have hsamevar : |vectorColeHopfStep vq (s.m (k+1-j)) (vectorTailRecursion s β t r p j) x-
        vectorColeHopfStep vr (s.m (k+1-j)) (vectorTailRecursion s β t r p j) x| ≤
        (n : ℝ)/2*(vq-vr) := by
      rw [abs_of_nonneg hvary.1]
      exact hvary.2
    rw [vectorTailRecursion,vectorTailRecursion]
    calc
      _ ≤ |vectorColeHopfStep vq (s.m (k+1-j)) (vectorTailRecursion s β t q p j) x-
          vectorColeHopfStep vq (s.m (k+1-j)) (vectorTailRecursion s β t r p j) x|+
        |vectorColeHopfStep vq (s.m (k+1-j)) (vectorTailRecursion s β t r p j) x-
          vectorColeHopfStep vr (s.m (k+1-j)) (vectorTailRecursion s β t r p j) x| := abs_sub_le _ _ _
      _ ≤ R+(n : ℝ)/2*(vq-vr) := add_le_add hsame hsamevar
      _ = _ := by
        rw [show k+2-(j+1)=k+1-j by omega]
        dsimp only [R,c,vq,vr]
        ring

theorem vectorTailRecursion_time_abs_sub_le {n k : ℕ} (s : RSBScheme k)
    (β t q r : ℝ) (ht : t ≤ 1) (hq : q∈Icc (0 : ℝ) 1) (hr : r∈Icc (0 : ℝ) 1)
    (p : Couplings n×ℝ) (x : Field n) :
    |vectorTailRecursion s β t q p (k+2) x-vectorTailRecursion s β t r p (k+2) x| ≤
      (n : ℝ)*((1-t)*β^2)/2*|q-r| := by
  rcases le_total q r with h|h
  · have hh := vectorTailRecursion_time_partial_abs_sub_le s β t q r ht hq hr h p le_rfl x
    simp only [Nat.sub_self,s.q_zero,max_eq_left hr.1,max_eq_left hq.1] at hh
    rw [abs_sub_comm q r,abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh
  · rw [abs_sub_comm (vectorTailRecursion s β t q p (k+2) x)
      (vectorTailRecursion s β t r p (k+2) x)]
    have hh := vectorTailRecursion_time_partial_abs_sub_le s β t r q ht hr hq h p le_rfl x
    simp only [Nat.sub_self,s.q_zero,max_eq_left hq.1,max_eq_left hr.1] at hh
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    exact hh

end QuantitativePaper
