module
public import FourPapersCommon.EuclideanOperatorMatrix
public import QuantitativePaper.ResponseGeneratorAlgebra

@[expose] public section

/-! Exact Euclidean trace conversion for the second-order chain rule. -/
noncomputable section
open scoped BigOperators ContDiff Matrix.Norms.Elementwise
namespace FourPapersCommon
open QuantitativeFollowup QuantitativePaper
set_option maxHeartbeats 1500000
set_option maxSynthPendingDepth 128
variable {n : ℕ}
local notation "Vec" => EuclideanSpace ℝ (Fin n)

theorem sum_second_hessian_pushforward (U Z : Vec→ℝ) (x m : Vec)
    (hU : ContDiffAt ℝ 2 U x) :
    (∑i : Fin n,fderiv ℝ (fderiv ℝ Z) m
      (hessianOperator U x (EuclideanSpace.single i 1))
      (hessianOperator U x (EuclideanSpace.single i 1)))=
      responseMatrixPair (euclideanOperatorMatrix (hessianOperator U x)*
        euclideanOperatorMatrix (hessianOperator U x))
        (euclideanOperatorMatrix (hessianOperator Z m)) := by
  let H:=hessianOperator U x
  let A:=hessianOperator Z m
  have hs (v w : Vec) : inner ℝ (H v) w=inner ℝ v (H w) := by
    calc
      _ = inner ℝ (H w) v := by
        dsimp only [H]
        rw [inner_hessianOperator,inner_hessianOperator]
        exact (hU.isSymmSndFDerivAt (by norm_num)).eq v w
      _ = _ := real_inner_comm _ _
  have hmatrix:=euclideanOperatorMatrix_hessian_symmetric U x hU
  calc
    _ = ∑i : Fin n,inner ℝ (A (H (EuclideanSpace.single i 1)))
        (H (EuclideanSpace.single i 1)) := by simp only [inner_hessianOperator,A,H]
    _ = ∑i : Fin n,inner ℝ (H (A (H (EuclideanSpace.single i 1))))
        (EuclideanSpace.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hs (A (H (EuclideanSpace.single i 1))) (EuclideanSpace.single i 1)).symm
    _ = Matrix.trace (euclideanOperatorMatrix H*euclideanOperatorMatrix A*
        euclideanOperatorMatrix H) := by
      rw [←euclideanOperatorMatrix_mul,←euclideanOperatorMatrix_mul]
      simp only [Matrix.trace,euclideanOperatorMatrix,ContinuousLinearMap.mul_apply,
        Matrix.diag_apply,EuclideanSpace.inner_single_right,starRingEnd_apply,star_trivial,one_mul]
    _ = Matrix.trace (euclideanOperatorMatrix H*euclideanOperatorMatrix H*
        euclideanOperatorMatrix A) := by
      simpa only [Matrix.mul_assoc] using Matrix.trace_mul_cycle'
        (euclideanOperatorMatrix H) (euclideanOperatorMatrix A) (euclideanOperatorMatrix H)
    _ = _ := by
      unfold responseMatrixPair
      rw [Matrix.transpose_mul,hmatrix.eq]

end FourPapersCommon
