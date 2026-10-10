module
public import QuantitativePaper.VectorFiniteCellItoTest

@[expose] public section

/-! Exact cancellation of the genuine finite-cell time derivative and the
Gaussian Laplacian. This is an identity of the actual Frechet jets. -/
noncomputable section
open MeasureTheory Set FourPapersCommon
open scoped NNReal ContDiff BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 500000
set_option maxSynthPendingDepth 128

theorem vectorBilinearTrace_hessian_eq_laplacian {n : ℕ} (f : Field n→ℝ) (x : Field n) :
    vectorBilinearTrace (vectorHessian f x)=vectorLaplacian f x := rfl

theorem finiteGaussianGenerator_euclidean {n : ℕ} (f : Field n→ℝ) (m : ℝ) (x : Field n) :
    finiteGaussianGenerator f (fun l : Fin n => EuclideanSpace.single l (1 : ℝ)) m x=
      vectorLaplacian f x+m*‖gradient f x‖^2 := by
  unfold finiteGaussianGenerator
  rw [Finset.sum_add_distrib]
  simp_rw [←gradient_euclidean_coordinate]
  rw [←Finset.mul_sum,←EuclideanSpace.real_norm_sq_eq]
  rfl

theorem vectorFiniteCellTimeField_generator_cancel {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (p : Couplings n×ℝ) (i : ℕ) (q : ℝ) (x : Field n) :
    vectorFiniteCellTimeField s β t p i q x+((1-t)*β^2)/2*
      vectorBilinearTrace (vectorHessian (vectorFiniteCellPotential s β t p i q) x)=
      -((1-t)*β^2)/2*(s.m i)*‖gradient (vectorFiniteCellPotential s β t p i q) x‖^2 := by
  rw [vectorFiniteCellTimeField_eq_generator,finiteGaussianGenerator_euclidean,
    vectorBilinearTrace_hessian_eq_laplacian]
  ring

end QuantitativePaper
