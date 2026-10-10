module
public import QuantitativePaper.VectorBackwardLinear
public import QuantitativePaper.VectorCovarianceTrace
public import QuantitativePaper.VectorFieldConditionalVariance

@[expose] public section

/-! The actual covariance matrix quadratic form equals the genuine terminal
field-direction variance. This makes the field-Hessian sandwich literal. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128

theorem fieldDot_sq_eq_double_sum {n : ℕ} (w : Field n) (σ : Configuration n) :
    fieldDot w σ^2=∑l : Fin n,∑j : Fin n,
      (w l*w j)*(Paper.spinSign (σ l)*Paper.spinSign (σ j)) := by
  unfold fieldDot
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorBackwardVariance_fieldDot_eq_sum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (w : Field n) :
    vectorBackwardVariance s β t (fun σ => fieldDot w σ) i x=
      ∑l : Fin n,∑j : Fin n,vectorSpinCovariance s β t i x l j*w l*w j := by
  have hs : (fun σ : Configuration n => fieldDot w σ^2)=
      fun σ => ∑l : Fin n,∑j : Fin n,(w l*w j)*(Paper.spinSign (σ l)*Paper.spinSign (σ j)) :=
    funext (fieldDot_sq_eq_double_sum w)
  unfold vectorBackwardVariance
  rw [hs,vectorBackwardMean_fieldDot]
  simp_rw [vectorBackwardMean_finset_sum,vectorBackwardMean_const_mul]
  rw [pow_two,Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑l : Fin n,∑j : Fin n,
        ((w l*w j)*vectorBackwardMean s β t
          (fun σ => Paper.spinSign (σ l)*Paper.spinSign (σ j)) i x-
          (w l*vectorMagnetization s β t x.1 (k+2-i) x.2 l)*
            (w j*vectorMagnetization s β t x.1 (k+2-i) x.2 j)) := by
      simp only [Finset.sum_sub_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro j _
      unfold vectorSpinCovariance
      ring

theorem vectorObservableCovariance_fieldDot_eq_sum {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (w : Field n) :
    vectorObservableCovariance s β t x.1 (fun σ => fieldDot w σ) (k+2-i) 0 x.2=
      ∑l : Fin n,∑j : Fin n,vectorSpinCovariance s β t i x l j*w l*w j :=
  (vectorBackwardVariance_eq_observableCovariance s β t _ i x).symm.trans
    (vectorBackwardVariance_fieldDot_eq_sum s β t i x w)

theorem vectorSpinCovariance_quadratic_nonneg {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (w : Field n) :
    0≤∑l : Fin n,∑j : Fin n,vectorSpinCovariance s β t i x l j*w l*w j := by
  rw [←vectorObservableCovariance_fieldDot_eq_sum]
  let R : ℝ≥0 := (Real.sqrt (n : ℝ)*‖w‖).toNNReal
  have hb (σ : Configuration n) : |fieldDot w σ|≤R := by
    change |fieldDot w σ|≤((Real.sqrt (n : ℝ)*‖w‖).toNNReal : ℝ)
    rw [Real.coe_toNNReal _ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    exact abs_fieldDot w σ
  exact vectorObservableCovariance_nonneg s β t x.1 _ R hb _ 0 x.2

theorem vectorHessianMatrix_covariance_quadratic_bounds {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (w : Field n) :
    observableDepthMass s (k+2-i)*
        (∑l : Fin n,∑j : Fin n,vectorSpinCovariance s β t i x l j*w l*w j) ≤
      ∑l : Fin n,∑j : Fin n,vectorFieldHessianMatrix s β t i x l j*w l*w j ∧
    (∑l : Fin n,∑j : Fin n,vectorFieldHessianMatrix s β t i x l j*w l*w j) ≤
      ∑l : Fin n,∑j : Fin n,vectorSpinCovariance s β t i x l j*w l*w j := by
  have hh := vectorFieldHessian_covariance_quadratic_bounds s β t x.1 (k+2-i) x.2 w
  rw [vectorObservableCovariance_fieldDot_eq_sum,
    euclidean_clm_quadratic_eq_sum] at hh
  exact hh

end QuantitativePaper
