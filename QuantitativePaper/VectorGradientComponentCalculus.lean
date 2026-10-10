module
public import QuantitativePaper.VectorMeasureHessianEnergy
public import QuantitativePaper.VectorFiniteCellGradientBounds

@[expose] public section

/-! Literal gradient-coordinate derivatives and Hilbert-square contraction
of the actual Hessian. -/
noncomputable section
open scoped ContDiff BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem fderiv_gradient_component_eq_hessian (f : Field n→ℝ) (hf : ContDiff ℝ 2 f)
    (x w : Field n) (l : Fin n) :
    fderiv ℝ (fun y=>gradient f y l) x w=hessianOperator f x w l := by
  have hd := (EuclideanSpace.proj l).hasFDerivAt.comp x
    (hasFDerivAt_gradient_hessianOperator f hf x)
  change HasFDerivAt (fun y=>gradient f y l) ((EuclideanSpace.proj l).comp (hessianOperator f x)) x at hd
  exact congrArg (fun A : Field n→L[ℝ]ℝ=>A w) hd.fderiv

theorem sum_gradient_component_energy_eq_hilbertSquare (f : Field n→ℝ)
    (hf : ContDiff ℝ 2 f) (x : Field n) :
    (∑l : Fin n,∑j : Fin n,(fderiv ℝ (fun y=>gradient f y l) x (EuclideanSpace.single j 1))^2)=
      vectorHessianHilbertSquare (hessianOperator f x) := by
  simp_rw [fderiv_gradient_component_eq_hessian f hf]
  rw [Finset.sum_comm]
  unfold vectorHessianHilbertSquare
  apply Finset.sum_congr rfl
  intro j _
  rw [EuclideanSpace.real_norm_sq_eq]

end QuantitativePaper
