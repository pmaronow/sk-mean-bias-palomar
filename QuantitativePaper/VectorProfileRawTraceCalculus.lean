module
public import QuantitativePaper.VectorFiniteHessianReaction
public import FourPapersCommon.EuclideanOperatorTrace
public import FourPapersCommon.LocalGradientCalculus

@[expose] public section

/-! Coordinate trace and finite-sum calculus for the actual Hessian. -/
noncomputable section
open Set Filter
open scoped ContDiff BigOperators
namespace QuantitativePaper
open FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 1200000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem euclideanOperatorTrace_hessian_eq_laplacian (U : Field n → ℝ) (x : Field n) :
    euclideanOperatorTrace (hessianOperator U x)=vectorLaplacian U x := by
  unfold euclideanOperatorTrace Matrix.trace euclideanOperatorMatrix vectorLaplacian
  exact Finset.sum_congr rfl (fun l _=>hessianOperator_euclidean_diagonal U x l)

theorem vectorLinearBackwardGenerator_fin_sum {ι : Type*} (S : Finset ι)
    (A : ι → Field n → ℝ) (U : Field n → ℝ)
    (hA : ∀ l ∈ S, ContDiff ℝ 2 (A l)) (m : ℝ) (x : Field n) :
    vectorLinearBackwardGenerator (fun y=>∑l∈S,A l y) U m x=
      ∑l∈S,vectorLinearBackwardGenerator (A l) U m x := by
  have hD : fderiv ℝ (fun y=>∑l∈S,A l y)=fun y=>∑l∈S,fderiv ℝ (A l) y :=
    funext fun y=>fderiv_fun_sum (fun l hl=>(hA l hl).differentiable (by norm_num) y)
  have hDA (l : ι) (hl : l∈S) : Differentiable ℝ (fderiv ℝ (A l)):=
    ((hA l hl).fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  unfold vectorLinearBackwardGenerator vectorBilinearTrace vectorHessian
  rw [hD,fderiv_fun_sum (fun l hl=>hDA l hl x)]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.sum_comm,Finset.sum_div,Finset.sum_add_distrib]

theorem euclideanOperatorTrace_hessian_square_eq (U : Field n → ℝ) (x : Field n)
    (hU : ContDiffAt ℝ 2 U x) :
    euclideanOperatorTrace (hessianOperator U x*hessianOperator U x)=
      ∑l : Fin n,∑j : Fin n,
        (fderiv ℝ (fun y=>gradient U y l) x (EuclideanSpace.single j 1))^2 := by
  have hG:=hasFDerivAt_gradient_of_contDiffAt U x hU
  have hcoord (l j : Fin n) :
      fderiv ℝ (fun y=>gradient U y l) x (EuclideanSpace.single j 1)=
        euclideanOperatorMatrix (hessianOperator U x) l j := by
    exact congrArg (fun L : Field n→L[ℝ]ℝ=>L (EuclideanSpace.single j 1))
      (((EuclideanSpace.proj l).hasFDerivAt.comp x hG).fderiv)
  simp_rw [hcoord]
  unfold euclideanOperatorTrace
  rw [euclideanOperatorMatrix_mul]
  unfold Matrix.trace
  simp only [Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  have hs:=congrFun (congrFun (euclideanOperatorMatrix_hessian_symmetric U x hU) j) l
  change euclideanOperatorMatrix (hessianOperator U x) l j=
    euclideanOperatorMatrix (hessianOperator U x) j l at hs
  rw [←hs,pow_two]

end QuantitativePaper
