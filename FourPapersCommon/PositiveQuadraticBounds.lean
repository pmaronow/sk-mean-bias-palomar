module
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! Finite-sum and trace bounds for a genuine positive semidefinite quadratic
form, using its positive square root on the ordinary Euclidean space. -/
noncomputable section
open Matrix
open scoped BigOperators MatrixOrder
namespace FourPapersCommon
set_option maxHeartbeats 1000000

theorem positive_matrix_quadratic_eq_sqrt_norm_sq {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (v : EuclideanSpace ℝ I) :
    (∑i : I,∑j : I,C i j*v i*v j)=‖(CFC.sqrt C).toEuclideanLin v‖^2 := by
  let B := CFC.sqrt C
  have hB : B.conjTranspose=B := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C)).isHermitian.eq
  have hs : B.conjTranspose*B=C := by rw [hB];exact CFC.sqrt_mul_sqrt_self C hC.nonneg
  have hT : B.conjTranspose=B.transpose := by ext i j;simp
  have hinner : v ⬝ᵥ (C *ᵥ v)=(B *ᵥ v) ⬝ᵥ (B *ᵥ v) := by
    rw [←hs,←Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,hT,Matrix.vecMul_transpose]
  calc
    _ = v ⬝ᵥ (C *ᵥ v) := by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (B *ᵥ v) ⬝ᵥ (B *ᵥ v) := hinner
    _ = ‖(CFC.sqrt C).toEuclideanLin v‖^2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp only [dotProduct,pow_two]
      rfl

theorem positive_matrix_quadratic_sum_le {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (b : J→EuclideanSpace ℝ I) :
    (∑i : I,∑j : I,C i j*(∑k : J,b k) i*(∑k : J,b k) j)≤
      (Fintype.card J:ℝ)*∑k : J,∑i : I,∑j : I,C i j*b k i*b k j := by
  classical
  simp_rw [positive_matrix_quadratic_eq_sqrt_norm_sq C hC]
  rw [map_sum]
  calc
    _ ≤ (∑k : J,‖(CFC.sqrt C).toEuclideanLin (b k)‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
        (fun _ : J=>(1:ℝ)) (fun k=>‖(CFC.sqrt C).toEuclideanLin (b k)‖)
      simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] using h

theorem positive_matrix_quadratic_le_trace {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (hC : C.PosSemidef) (w : EuclideanSpace ℝ I) :
    (∑i : I,∑j : I,C i j*w i*w j)≤Matrix.trace C*‖w‖^2 := by
  classical
  let L := (CFC.sqrt C).toEuclideanLin
  have hb (i : I) : ‖L (EuclideanSpace.single i 1)‖^2=C i i := by
    rw [←positive_matrix_quadratic_eq_sqrt_norm_sq C hC]
    simp
  have hw : w=∑i : I,(w i) • EuclideanSpace.single i 1 := by
    ext j
    simp [Pi.single_apply]
  calc
    _ = ‖L w‖^2 := positive_matrix_quadratic_eq_sqrt_norm_sq C hC w
    _ ≤ (∑i : I,|w i| * ‖L (EuclideanSpace.single i 1)‖)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      conv_lhs => rw [hw,map_sum]
      exact (norm_sum_le _ _).trans_eq (by simp only [map_smul,norm_smul,Real.norm_eq_abs])
    _ ≤ (∑i : I,|w i|^2)*(∑i : I,‖L (EuclideanSpace.single i 1)‖^2) :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = _ := by simp only [sq_abs,hb,Matrix.trace,Matrix.diag,EuclideanSpace.real_norm_sq_eq];ring

end FourPapersCommon
