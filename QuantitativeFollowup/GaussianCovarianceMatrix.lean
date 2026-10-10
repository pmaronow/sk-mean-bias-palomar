module
public import QuantitativeFollowup.GaussianScoreCovarianceResponse
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

/-! Coordinates of a genuine linear Gaussian covariance curve and its
symmetric Hessian contraction. This identifies the covariance term with
the literal half-double-sum in the finite-profile response calculation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativeFollowup
open QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def gaussianLinearCovariance (A : Field n →L[ℝ] Field m) (i j : Fin m) : ℝ :=
  ∑l : Fin n,A (EuclideanSpace.single l 1) i*A (EuclideanSpace.single l 1) j

def gaussianLinearCovarianceDirection (A B : Field n →L[ℝ] Field m) (i j : Fin m) : ℝ :=
  ∑l : Fin n,(B (EuclideanSpace.single l 1) i*A (EuclideanSpace.single l 1) j+
    A (EuclideanSpace.single l 1) i*B (EuclideanSpace.single l 1) j)

theorem hasDerivAt_gaussianLinearCovariance (A : ℝ → Field n →L[ℝ] Field m)
    (B : Field n →L[ℝ] Field m) (a : ℝ) (hA : HasDerivAt A B a) (i j : Fin m) :
    HasDerivAt (fun u => gaussianLinearCovariance (A u) i j)
      (gaussianLinearCovarianceDirection (A a) B i j) a := by
  unfold gaussianLinearCovariance gaussianLinearCovarianceDirection
  apply HasDerivAt.fun_sum
  intro l _
  have hi : HasDerivAt (fun u => A u (EuclideanSpace.single l 1) i)
      (B (EuclideanSpace.single l 1) i) a := by
    convert! (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt.comp_hasDerivAt a
      (hA.clm_apply (hasDerivAt_const a (EuclideanSpace.single l 1))) using 1
    simp only [map_zero,add_zero,PiLp.proj_apply]
  have hj : HasDerivAt (fun u => A u (EuclideanSpace.single l 1) j)
      (B (EuclideanSpace.single l 1) j) a := by
    convert! (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) j).hasFDerivAt.comp_hasDerivAt a
      (hA.clm_apply (hasDerivAt_const a (EuclideanSpace.single l 1))) using 1
    simp only [map_zero,add_zero,PiLp.proj_apply]
  exact hi.mul hj

theorem field_bilinear_basis_expansion (H : Field m →L[ℝ] Field m →L[ℝ] ℝ)
    (u v : Field m) :
    H u v=∑i : Fin m,∑j : Fin m,u i*v j*H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  have hu := field_clm_basis_expansion (H.flip v) u
  simp only [ContinuousLinearMap.flip_apply,EuclideanSpace.basisFun_apply] at hu
  rw [hu]
  apply Finset.sum_congr rfl
  intro i _
  rw [field_clm_basis_expansion (H (EuclideanSpace.single i 1)) v,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by simp only [EuclideanSpace.basisFun_apply];ring)

theorem gaussian_covariance_bilinear_contraction (A B : Field n →L[ℝ] Field m)
    (H : Field m →L[ℝ] Field m →L[ℝ] ℝ)
    (hH : ∀u v,H u v=H v u) :
    (∑l : Fin n,H (A (EuclideanSpace.single l 1)) (B (EuclideanSpace.single l 1)))=
      (1/2 : ℝ)*∑i : Fin m,∑j : Fin m,gaussianLinearCovarianceDirection A B i j*
        H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
  classical
  have ht : (∑l : Fin n,H (A (EuclideanSpace.single l 1)) (B (EuclideanSpace.single l 1)))=
      ∑i : Fin m,∑j : Fin m,∑l : Fin n,
        A (EuclideanSpace.single l 1) i*B (EuclideanSpace.single l 1) j*
          H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [show (∑l : Fin n,H (A (EuclideanSpace.single l 1)) (B (EuclideanSpace.single l 1)))=
        ∑l : Fin n,∑i : Fin m,∑j : Fin m,
          A (EuclideanSpace.single l 1) i*B (EuclideanSpace.single l 1) j*
            H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) from
      Finset.sum_congr rfl (fun l _ => field_bilinear_basis_expansion H _ _)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  have hs : (∑i : Fin m,∑j : Fin m,∑l : Fin n,
      B (EuclideanSpace.single l 1) i*A (EuclideanSpace.single l 1) j*
        H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))=
      ∑i : Fin m,∑j : Fin m,∑l : Fin n,
        A (EuclideanSpace.single l 1) i*B (EuclideanSpace.single l 1) j*
          H (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun l _ => by rw [hH];ring)
  rw [ht]
  simp only [gaussianLinearCovarianceDirection,Finset.sum_mul,add_mul,Finset.sum_add_distrib]
  rw [hs]
  ring

def gaussianScoreOperator (V F : Field m → ℝ) (x : Field m) (c : ℝ) :
    Field m →L[ℝ] Field m →L[ℝ] ℝ :=
  Real.exp (-V x) • (vectorHessian (fun y => Real.exp (V y)*F y) x-
    c • vectorHessian (fun y => Real.exp (V y)) x)

theorem gaussianScoreOperator_apply (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (x u v : Field m) (c : ℝ) :
    gaussianScoreOperator V F x c u v=gaussianScoreBilinear V F x u v c := by
  simp only [gaussianScoreOperator,smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul]
  rw [←gaussianScoreBilinear_exp_identity V F hV hF x u v c]
  rw [←mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul]

theorem gaussianScoreOperator_symmetric (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (x : Field m) (c : ℝ) :
    ∀u v,gaussianScoreOperator V F x c u v=gaussianScoreOperator V F x c v u := by
  intro u v
  simp only [gaussianScoreOperator,smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul]
  rw [show vectorHessian (fun y => Real.exp (V y)*F y) x u v=
      vectorHessian (fun y => Real.exp (V y)*F y) x v u from
        ((hV.exp.mul hF).contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v,
    show vectorHessian (fun y => Real.exp (V y)) x u v=
      vectorHessian (fun y => Real.exp (V y)) x v u from
        (hV.exp.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v]

theorem gaussian_covariance_score_contraction (V F : Field m → ℝ)
    (hV : ContDiff ℝ 2 V) (hF : ContDiff ℝ 2 F) (x : Field m) (c : ℝ)
    (A B : Field n →L[ℝ] Field m) :
    (∑l : Fin n,gaussianScoreBilinear V F x (A (EuclideanSpace.single l 1))
      (B (EuclideanSpace.single l 1)) c)=
      (1/2 : ℝ)*∑i : Fin m,∑j : Fin m,gaussianLinearCovarianceDirection A B i j*
        gaussianScoreBilinear V F x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) c := by
  simpa only [gaussianScoreOperator_apply V F hV hF] using
    gaussian_covariance_bilinear_contraction A B (gaussianScoreOperator V F x c)
      (gaussianScoreOperator_symmetric V F hV hF x c)

end QuantitativeFollowup
