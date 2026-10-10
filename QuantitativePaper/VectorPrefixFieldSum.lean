module
public import QuantitativePaper.VectorSitePrefixFunctions
public import QuantitativePaper.VectorIncidentEdges

@[expose] public section

/-! Literal field coordinates and accumulated variance of the actual
Gaussian prefix, including repeated nodes and zero-variance intervals. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000

def prefixFieldIncrement {k : ℕ} (s : RSBScheme k) (β t : ℝ) (j : ℕ) : ℝ :=
  if j ≤ k+1 then Real.sqrt ((1-t)*(β^2*(s.q (j+1)-s.q j))) else 0

theorem vectorCoordinateUpdate_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (j : ℕ) (x : VectorState n) (z : Field n) :
    (vectorCoordinateUpdate s β t j x z).2 = x.2 + prefixFieldIncrement s β t j • z := by
  unfold vectorCoordinateUpdate prefixFieldIncrement
  split_ifs
  · rfl
  · simp

theorem vectorPrefixHistory_final_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N : ℕ) (p : VectorPrefixCoordinates n N) :
    (vectorPrefixHistory s β t N p (Fin.last N)).2 =
      ∑ j : Fin N, prefixFieldIncrement s β t j • p.2 j := by
  induction N with
  | zero => simp [vectorPrefixHistory,independentHistory]
  | succ N ih =>
    let p0 : VectorPrefixCoordinates n N := (p.1, fun j => p.2 j.castSucc)
    simp only [vectorPrefixHistory, independentHistory, Fin.snoc_last]
    change (vectorCoordinateUpdate s β t N
      (vectorPrefixHistory s β t N p0 (Fin.last N)) (p.2 (Fin.last N))).2 = _
    rw [vectorCoordinateUpdate_field, ih p0, Fin.sum_univ_castSucc]
    rfl

theorem vectorPrefixEuclideanHistory_final_field {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (N : ℕ) (g : VectorPrefixGaussianSpace n N) :
    (vectorPrefixEuclideanHistory s β t N g (Fin.last N)).2 =
      ∑ j : Fin N, prefixFieldIncrement s β t j •
        WithLp.toLp 2 (fun i : Fin n => g (.inr (j,i))) := by
  rw [vectorPrefixEuclideanHistory_apply,vectorPrefixHistory_final_field]
  rfl

theorem prefixFieldIncrement_square {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (ht : t ≤ 1) (j : ℕ) (hj : j ≤ k+1) :
    (prefixFieldIncrement s β t j)^2 = (1-t)*β^2*(s.q (j+1)-s.q j) := by
  unfold prefixFieldIncrement
  rw [if_pos hj,Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr ht)
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (s.q_mono j hj))))]
  ring

theorem prefixFieldIncrement_sum_square {k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (ht : t ≤ 1) (N : ℕ) (hN : N ≤ k+2) :
    (∑ j : Fin N, (prefixFieldIncrement s β t j)^2) = (1-t)*β^2*s.q N := by
  induction N with
  | zero => simp [s.q_zero]
  | succ N ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [ih (by omega),prefixFieldIncrement_square s β t ht N (by omega)]
    ring

end QuantitativePaper
