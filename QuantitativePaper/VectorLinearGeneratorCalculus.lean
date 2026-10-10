module
public import QuantitativePaper.VectorJointResponseSquareInterval

@[expose] public section

/-! Literal linear backward generator calculus for genuine C2 fields. -/
noncomputable section
open scoped ContDiff BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 700000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorLinearBackwardGenerator_sub (A B U : Field n→ℝ)
    (hA : ContDiff ℝ 2 A) (hB : ContDiff ℝ 2 B) (m : ℝ) (x : Field n) :
    vectorLinearBackwardGenerator (fun y=>A y-B y) U m x=
      vectorLinearBackwardGenerator A U m x-vectorLinearBackwardGenerator B U m x := by
  have hDA : Differentiable ℝ (fderiv ℝ A):=
    (hA.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hDB : Differentiable ℝ (fderiv ℝ B):=
    (hB.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun y=>A y-B y)=fun y=>fderiv ℝ A y-fderiv ℝ B y:=
    funext fun y=>fderiv_fun_sub (hA.differentiable (by norm_num) y) (hB.differentiable (by norm_num) y)
  unfold vectorLinearBackwardGenerator vectorBilinearTrace vectorHessian
  rw [hD,fderiv_fun_sub (hDA x) (hDB x)]
  simp only [ContinuousLinearMap.sub_apply,Finset.sum_sub_distrib]
  ring

theorem vectorLinearBackwardGenerator_const_mul (B U : Field n→ℝ)
    (hB : ContDiff ℝ 2 B) (m d : ℝ) (x : Field n) :
    vectorLinearBackwardGenerator (fun y=>d*B y) U m x=d*vectorLinearBackwardGenerator B U m x := by
  have hDB : Differentiable ℝ (fderiv ℝ B):=
    (hB.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hD : fderiv ℝ (fun y=>d*B y)=fun y=>d • fderiv ℝ B y:=
    funext fun y=>by
      exact ((hB.differentiable (by norm_num) y).hasFDerivAt.const_smul d).fderiv
  unfold vectorLinearBackwardGenerator vectorBilinearTrace vectorHessian
  rw [hD,fderiv_fun_const_smul (hDB x) d]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,←Finset.mul_sum]
  ring

theorem vectorLinearBackwardGenerator_square (g U : Field n→ℝ)
    (hg : ContDiff ℝ 2 g) (m : ℝ) (x : Field n) :
    vectorLinearBackwardGenerator (fun y=>g y^2) U m x=
      2*g x*vectorLinearBackwardGenerator g U m x+
        ∑l : Fin n,(fderiv ℝ g x (EuclideanSpace.single l 1))^2 := by
  unfold vectorLinearBackwardGenerator
  rw [fderiv_square g (hg.differentiable (by norm_num)),vectorBilinearTrace_square g hg]
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul]
  ring

end QuantitativePaper
