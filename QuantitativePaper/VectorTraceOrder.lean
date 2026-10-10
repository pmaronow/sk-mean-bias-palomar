module
public import QuantitativePaper.VectorCovarianceQuadratic
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-! Actual covariance/Hessian positive semidefinite matrices and their trace
comparison. The quadratic sandwich is derived from the concrete response
recursion, including the mass-zero case. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Matrix
open scoped BigOperators MatrixOrder
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000

theorem matrix_trace_mul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A*B) := by
  have h := (hA.mul_mul_conjTranspose_same (CFC.sqrt B)).trace_nonneg
  have hs : (CFC.sqrt B).conjTranspose=CFC.sqrt B :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)).isHermitian.eq
  rw [hs,Matrix.trace_mul_cycle,Matrix.trace_mul_cycle,Matrix.mul_assoc,
    CFC.sqrt_mul_sqrt_self B hB.nonneg] at h
  exact h

theorem real_matrix_quadratic_eq_sum {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    star v ⬝ᵥ (A *ᵥ v)=∑l,∑j,A l j*v l*v j := by
  classical
  simp only [dotProduct,Matrix.mulVec,star_trivial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem vectorFieldHessianMatrix_symmetric {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) (l j : Fin n) :
    vectorFieldHessianMatrix s β t i x l j=vectorFieldHessianMatrix s β t i x j l := by
  simp only [vectorFieldHessianMatrix,vectorFieldHessian_component_eq_joint]
  exact ((contDiff_vectorRecursion_joint s β t (k+2-i)).contDiffAt.isSymmSndFDerivAt
    (by simp)).eq (vectorJointCoordinateDirection n j) (vectorJointCoordinateDirection n l)

theorem vectorSpinCovariance_posSemidef {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) :
    (vectorSpinCovariance s β t i x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext l j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using
      vectorSpinCovariance_symmetric s β t i x j l
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    exact vectorSpinCovariance_quadratic_nonneg s β t i x (WithLp.toLp 2 v)

theorem vectorFieldHessianMatrix_posSemidef {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) :
    (vectorFieldHessianMatrix s β t i x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext l j
    simpa only [Matrix.conjTranspose_apply,star_trivial] using
      vectorFieldHessianMatrix_symmetric s β t i x j l
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    exact le_trans (mul_nonneg (observableDepthMass_nonneg s (k+2-i))
      (vectorSpinCovariance_quadratic_nonneg s β t i x (WithLp.toLp 2 v)))
      (vectorHessianMatrix_covariance_quadratic_bounds s β t i x (WithLp.toLp 2 v)).1

theorem vectorFieldHessianMatrix_sub_mass_covariance_posSemidef {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) :
    (vectorFieldHessianMatrix s β t i x-
      observableDepthMass s (k+2-i) • vectorSpinCovariance s β t i x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (vectorFieldHessianMatrix_posSemidef s β t i x).isHermitian.sub
      ((vectorSpinCovariance_posSemidef s β t i x).isHermitian.smul
        (IsSelfAdjoint.of_nonneg (observableDepthMass_nonneg s (k+2-i))))
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul,sub_mul,Finset.sum_sub_distrib]
    simp_rw [mul_assoc,←Finset.mul_sum]
    have h := (vectorHessianMatrix_covariance_quadratic_bounds s β t i x (WithLp.toLp 2 v)).1
    simpa only [WithLp.ofLp_toLp,mul_assoc] using sub_nonneg.mpr h

theorem vectorCovariance_sub_fieldHessianMatrix_posSemidef {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) :
    (vectorSpinCovariance s β t i x-vectorFieldHessianMatrix s β t i x).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · exact (vectorSpinCovariance_posSemidef s β t i x).isHermitian.sub
      (vectorFieldHessianMatrix_posSemidef s β t i x).isHermitian
  · intro v
    rw [real_matrix_quadratic_eq_sum]
    simp only [Matrix.sub_apply,sub_mul,Finset.sum_sub_distrib]
    exact sub_nonneg.mpr
      (vectorHessianMatrix_covariance_quadratic_bounds s β t i x (WithLp.toLp 2 v)).2

theorem vector_trace_covariance_order {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i : ℕ) (x : VectorState n) :
    let H := vectorFieldHessianMatrix s β t i x
    let C := vectorSpinCovariance s β t i x
    let m := observableDepthMass s (k+2-i)
    0 ≤ Matrix.trace (H*C) ∧
    m*Matrix.trace (H*C) ≤ Matrix.trace (H*H) ∧
    m*Matrix.trace (C*C) ≤ Matrix.trace (H*C) ∧
    Matrix.trace (H*C) ≤ Matrix.trace (C*C) := by
  dsimp only
  refine ⟨matrix_trace_mul_nonneg _ _ (vectorFieldHessianMatrix_posSemidef s β t i x)
    (vectorSpinCovariance_posSemidef s β t i x),?_,?_,?_⟩
  · have h := matrix_trace_mul_nonneg _ _ (vectorFieldHessianMatrix_posSemidef s β t i x)
      (vectorFieldHessianMatrix_sub_mass_covariance_posSemidef s β t i x)
    rw [Matrix.mul_sub,Matrix.mul_smul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at h
    linarith
  · have h := matrix_trace_mul_nonneg _ _
      (vectorFieldHessianMatrix_sub_mass_covariance_posSemidef s β t i x)
      (vectorSpinCovariance_posSemidef s β t i x)
    rw [Matrix.sub_mul,Matrix.smul_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at h
    linarith
  · have h := matrix_trace_mul_nonneg _ _
      (vectorCovariance_sub_fieldHessianMatrix_posSemidef s β t i x)
      (vectorSpinCovariance_posSemidef s β t i x)
    rw [Matrix.sub_mul,Matrix.trace_sub] at h
    linarith

end QuantitativePaper
