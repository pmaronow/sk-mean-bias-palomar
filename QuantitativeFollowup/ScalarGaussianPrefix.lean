module
public import QuantitativeFollowup.ScalarGaussianHistory
public import QuantitativeFollowup.GaussianCovarianceMatrix

@[expose] public section

/-! Literal cumulative Gaussian coordinates and their covariance. Zero
coefficients are included, so repeated nodes require no matrix inverse. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
namespace QuantitativeFollowup
open FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

 theorem scalarIndependentHistory_prefix (c : ℕ→ℝ) (n : ℕ) (z : Fin n→ℝ)
    (i : Fin (n+1)) :
    independentHistory (fun j x w => x+c j*w) n (0,z) i=
      ∑j : Fin n,if (j : ℕ) < (i : ℕ) then c j*z j else 0 := by
  induction n with
  | zero => simp [independentHistory]
  | succ n ih =>
    refine Fin.lastCases ?_ (fun l => ?_) i
    · simp only [independentHistory,Fin.snoc_last]
      rw [ih]
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last,Fin.val_castSucc]
      have he : (∑j : Fin n,if (j : ℕ) < n then c j*z j.castSucc else 0)=
          ∑j : Fin n,if (j : ℕ) < n+1 then c j*z j.castSucc else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [if_pos j.isLt,if_pos (by have := j.isLt;omega)]
      rw [he,if_pos (by omega : n < n+1)]
    · simp only [independentHistory,Fin.snoc_castSucc]
      rw [ih,Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc,Fin.val_last]
      rw [if_neg (by have := l.isLt;omega : ¬ n < (l : ℕ)),add_zero]

 def scalarCoefficientHistoryLinear (c : ℕ→ℝ) (n : ℕ) :
    QuantitativePaper.Field n→L[ℝ] QuantitativePaper.Field (n+1) :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1) => ℝ)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi fun i : Fin (n+1) =>
      ∑j : Fin n,if (j : ℕ) < (i : ℕ) then c j • PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin n=>ℝ) j else 0)

 theorem scalarCoefficientHistoryLinear_apply (c : ℕ→ℝ) (n : ℕ)
    (z : QuantitativePaper.Field n) (i : Fin (n+1)) :
    scalarCoefficientHistoryLinear c n z i=
      ∑j : Fin n,if (j : ℕ) < (i : ℕ) then c j*z j else 0 := by
  change (∑j : Fin n,if (j:ℕ) < (i:ℕ) then c j • PiLp.proj (𝕜:=ℝ) 2
    (fun _ : Fin n=>ℝ) j else 0) z=_
  rw [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (j : ℕ) < (i : ℕ)
  · simp [hj,PiLp.proj_apply]
  · simp [hj]

 theorem scalarCoefficientHistoryLinear_eq_history (β : ℝ) (T : ℕ→ℝ≥0) (n : ℕ) :
    scalarCoefficientHistoryLinear (fun j => Real.sqrt (β^2*((T (j+1):ℝ)-T j))) n=
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n+1)=>ℝ)).symm.toContinuousLinearMap).comp
        (scalarGaussianHistoryLinear β T n) := by
  ext z i
  rw [scalarCoefficientHistoryLinear_apply,ContinuousLinearMap.comp_apply,
    scalarGaussianHistoryLinear_apply]
  change (∑j : Fin n,if (j:ℕ) < (i:ℕ) then
    Real.sqrt (β^2*((T (j+1):ℝ)-T j))*z j else 0)=
      independentHistory (fun i x w => x+Real.sqrt (β^2*((T (i+1):ℝ)-T i))*w) n (0,WithLp.ofLp z) i
  exact (scalarIndependentHistory_prefix (fun j => Real.sqrt (β^2*((T (j+1):ℝ)-T j)))
    n (WithLp.ofLp z) i).symm

 theorem scalarCoefficientHistoryLinear_basis (c : ℕ→ℝ) (n : ℕ)
    (j : Fin n) (i : Fin (n+1)) :
    scalarCoefficientHistoryLinear c n (EuclideanSpace.single j 1) i=
      if (j : ℕ) < (i : ℕ) then c j else 0 := by
  rw [scalarCoefficientHistoryLinear_apply]
  rw [Finset.sum_eq_single j]
  · simp [PiLp.single_apply]
  · intro l _ hlj
    simp [PiLp.single_apply,Ne.symm hlj,hlj]
  · simp

 theorem scalarCoefficientHistoryLinear_covariance (c : ℕ→ℝ) (n : ℕ)
    (i j : Fin (n+1)) :
    gaussianLinearCovariance (scalarCoefficientHistoryLinear c n) i j=
      ∑l : Fin n,if (l : ℕ) < min (i : ℕ) (j : ℕ) then (c l)^2 else 0 := by
  unfold gaussianLinearCovariance
  apply Finset.sum_congr rfl
  intro l _
  simp only [scalarCoefficientHistoryLinear_basis,lt_min_iff]
  by_cases hi : (l : ℕ) < (i : ℕ) <;> by_cases hj : (l : ℕ) < (j : ℕ) <;> simp [hi,hj,pow_two]

end QuantitativeFollowup
