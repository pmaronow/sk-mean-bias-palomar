module
public import QuantitativeFollowup.ScalarGaussianPrefix

@[expose] public section

/-! Exact Brownian clock covariances of the explicit Gaussian history map.
Repeated times contribute zero and are retained without nondegeneracy inputs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

 theorem scalar_clock_increment_sum (β : ℝ) (T : ℕ→ℝ≥0) (m : ℕ) :
    (∑l∈Finset.range m,β^2*((T (l+1):ℝ)-T l))=β^2*((T m:ℝ)-T 0) := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ,ih];ring

 theorem scalarGaussianHistory_covariance (β : ℝ) (T : ℕ→ℝ≥0) (hT : Monotone T)
    (n : ℕ) (i j : Fin (n+1)) :
    gaussianLinearCovariance
      (scalarCoefficientHistoryLinear (fun l => Real.sqrt (β^2*((T (l+1):ℝ)-T l))) n) i j=
      β^2*(min (T i:ℝ) (T j:ℝ)-T 0) := by
  rw [scalarCoefficientHistoryLinear_covariance]
  have hs (l : ℕ) : (Real.sqrt (β^2*((T (l+1):ℝ)-T l)))^2=
      β^2*((T (l+1):ℝ)-T l) := Real.sq_sqrt
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hT (Nat.le_succ l))))
  simp_rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun l => if l < min (i:ℕ) (j:ℕ) then
    β^2*((T (l+1):ℝ)-T l) else 0)]
  have hm : min (i:ℕ) (j:ℕ)≤n := by have := i.isLt;have := j.isLt;omega
  have hr : (∑l∈Finset.range n,if l < min (i:ℕ) (j:ℕ) then
      β^2*((T (l+1):ℝ)-T l) else 0)=
      ∑l∈Finset.range (min (i:ℕ) (j:ℕ)),β^2*((T (l+1):ℝ)-T l) := by
    symm
    calc
      _=∑l∈Finset.range (min (i:ℕ) (j:ℕ)),if l < min (i:ℕ) (j:ℕ) then
        β^2*((T (l+1):ℝ)-T l) else 0 := by
        apply Finset.sum_congr rfl
        intro l hl
        rw [ite_eq_left (Finset.mem_range.mp hl)]
      _=∑l∈Finset.range n,if l < min (i:ℕ) (j:ℕ) then
        β^2*((T (l+1):ℝ)-T l) else 0 := by
        apply Finset.sum_subset (Finset.range_mono hm)
        intro l _ hl
        rw [ite_eq_right (by simpa only [Finset.mem_range] using hl)]
  rw [hr,scalar_clock_increment_sum]
  have hmin : (T (min (i:ℕ) (j:ℕ)):ℝ)=min (T i:ℝ) (T j:ℝ) := by
    by_cases hij : (i:ℕ)≤j
    · rw [min_eq_left hij,min_eq_left (NNReal.coe_le_coe.mpr (hT hij))]
    · have hji := le_of_not_ge hij
      rw [min_eq_right hji,min_eq_right (NNReal.coe_le_coe.mpr (hT hji))]
  rw [hmin]

 theorem scalarGaussianHistory_covariance_zero (β : ℝ) (T : ℕ→ℝ≥0) (hT : Monotone T)
    (h0 : T 0=0) (n : ℕ) (i j : Fin (n+1)) :
    gaussianLinearCovariance
      (scalarCoefficientHistoryLinear (fun l => Real.sqrt (β^2*((T (l+1):ℝ)-T l))) n) i j=
      β^2*min (T i:ℝ) (T j:ℝ) := by
  rw [scalarGaussianHistory_covariance β T hT n i j,h0,NNReal.coe_zero,sub_zero]

end QuantitativeFollowup
