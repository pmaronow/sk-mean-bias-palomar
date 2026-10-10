module
public import QuantitativePaper.VectorBinaryResponseBound
public import QuantitativePaper.VectorFieldConditionalVariance
public import QuantitativePaper.VectorSpatialStep

@[expose] public section

/-! Identification of the sharp spin-offset response with the actual
field Hessian and actual retained-disorder/field directions. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000

theorem vectorConditionalMean_joint_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p w : Couplings n × ℝ) (x v : Field n) (d : Configuration n → ℝ)
    (j : ℕ) (y : ℝ) :
    vectorConditionalMean s β t p (vectorTerminalExponent n β t w v) d j y x=
      vectorConditionalMean s β t (p+y • w) (fun _=>0) d j 0 (x+y • v) := by
  induction j generalizing x with
  | zero =>
    simp only [vectorConditionalMean,terminalTilt_zero]
    congr 1
    funext σ
    exact (vectorTerminalExponent_joint_line β t p w x v y σ).symm
  | succ j ih =>
    simp only [vectorConditionalMean,vectorPerturbedRecursion_zero]
    have hf : vectorPerturbedRecursion s β t p (vectorTerminalExponent n β t w v) j y=
      fun z=>vectorRecursion s β t (p+y • w) j (z+y • v):=by
      funext z
      exact vectorPerturbedRecursion_joint_line s β t p w z v j y
    have hv : vectorConditionalMean s β t p (vectorTerminalExponent n β t w v) d j y=
      fun z=>vectorConditionalMean s β t (p+y • w) (fun _=>0) d j 0 (z+y • v):=funext ih
    rw [hf,hv,vectorStepResponse_translate]

theorem vectorObservableCrossResponse_const_mul_right {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (c : ℝ)
    (j : ℕ) (y : ℝ) (x : Field n) :
    vectorObservableCrossResponse s β t p b (fun σ=>c*d σ) j y x=
      c*vectorObservableCrossResponse s β t p b d j y x := by
  let R : ℝ≥0:=(∑σ:Configuration n,|b σ|).toNNReal
  let S : ℝ≥0:=(∑σ:Configuration n,|d σ|).toNNReal
  have hb (σ:Configuration n) : |b σ|≤R:=by
    change |b σ|≤((∑σ:Configuration n,|b σ|).toNNReal:ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    exact Finset.single_le_sum (f:=fun τ:Configuration n=>|b τ|) (fun τ _=>abs_nonneg (b τ)) (Finset.mem_univ σ)
  have hd (σ:Configuration n) : |d σ|≤S:=by
    change |d σ|≤((∑σ:Configuration n,|d σ|).toNNReal:ℝ)
    rw [Real.coe_toNNReal _ (by positivity)]
    exact Finset.single_le_sum (f:=fun τ:Configuration n=>|d τ|) (fun τ _=>abs_nonneg (d τ)) (Finset.mem_univ σ)
  have hh:=hasDerivAt_vectorConditionalMean_offset s β t p b d R S hb hd j y x
  have he : (fun r=>vectorConditionalMean s β t p b (fun σ=>c*d σ) j r x)=
    fun r=>c*vectorConditionalMean s β t p b d j r x:=by
    funext r
    exact vectorConditionalMean_const_mul s β t p b d c j r x
  have hcd (σ:Configuration n) : |c*d σ|≤|c| *(S:ℝ):=by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hd σ) (abs_nonneg c)
  have hc:=hasDerivAt_vectorConditionalMean_offset s β t p b (fun σ=>c*d σ) R
    (|c| *(S:ℝ)).toNNReal hb (fun σ=>by
      rw [Real.coe_toNNReal _ (mul_nonneg (abs_nonneg c) S.coe_nonneg)]
      exact hcd σ) j y x
  rw [he] at hc
  exact hc.unique (hh.const_mul c)

theorem vectorObservableCrossResponse_const_mul_left_zero {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (b d : Configuration n → ℝ) (c : ℝ)
    (j : ℕ) (x : Field n) :
    vectorObservableCrossResponse s β t p (fun σ=>c*b σ) d j 0 x=
      c*vectorObservableCrossResponse s β t p b d j 0 x := by
  rw [vectorObservableCrossResponse_zero_symm,vectorObservableCrossResponse_const_mul_right,
    vectorObservableCrossResponse_zero_symm s β t p d b j x]

theorem vectorFieldHessian_diagonal_eq_secondResponse {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (j : ℕ) (x : Field n) (i : Fin n) :
    (vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i=
      vectorObservableSecondResponse s β t p (fun σ=>Paper.spinSign (σ i)) j 0 x := by
  have he : (fun σ:Configuration n=>fieldDot (EuclideanSpace.single i 1) σ)=
      fun σ=>Paper.spinSign (σ i):=by funext σ;simp [fieldDot]
  simpa only [EuclideanSpace.inner_single_left,map_one,one_mul,he] using
    vectorFieldHessian_quadratic_eq_secondResponse s β t p j x (EuclideanSpace.single i 1)

theorem spin_offset_derivative_le_fieldHessian {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p : Couplings n × ℝ) (d : Configuration n → ℝ) (hd : ∀σ,|d σ|≤1)
    (j : ℕ) (x : Field n) (i : Fin n) :
    |vectorObservableCrossResponse s β t p d (fun σ=>Paper.spinSign (σ i)) j 0 x|≤
      (vectorFieldHessian s β t p j x (EuclideanSpace.single i 1)) i := by
  rw [vectorFieldHessian_diagonal_eq_secondResponse]
  exact (binary_spin_offset_derivative_bound s β t p (fun σ=>Paper.spinSign (σ i)) d
    (fun σ=>by cases σ i <;> norm_num [Paper.spinSign]) hd j x).2

theorem hasDerivAt_vectorMagnetization_joint_line {n k : ℕ} (s : RSBScheme k) (β t : ℝ)
    (p w : Couplings n × ℝ) (x v : Field n) (j : ℕ) (i : Fin n) :
    HasDerivAt (fun y:ℝ=>vectorMagnetization s β t (p+y • w) j (x+y • v) i)
      (vectorObservableCrossResponse s β t p (vectorTerminalExponent n β t w v)
        (fun σ=>Paper.spinSign (σ i)) j 0 x) 0 := by
  have hh:=hasDerivAt_vectorConditionalMean_offset s β t p (vectorTerminalExponent n β t w v)
    (fun σ=>Paper.spinSign (σ i)) (jointDirectionBound β t (w,v)) 1
    (vectorTerminalExponent_le_jointDirectionBound β t (w,v)) (fun σ=>by simp) j 0 x
  have he : (fun y=>vectorConditionalMean s β t p (vectorTerminalExponent n β t w v)
      (fun σ=>Paper.spinSign (σ i)) j y x)=
    fun y=>vectorMagnetization s β t (p+y • w) j (x+y • v) i:=by
    funext y
    rw [vectorConditionalMean_joint_line]
    exact vectorConditionalMean_zero_eq_response s β t (p+y • w) _ j (x+y • v)
  rw [he] at hh
  exact hh

end QuantitativePaper
