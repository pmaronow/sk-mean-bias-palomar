module
public import QuantitativePaper.FiniteGeneratorBounds
public import QuantitativePaper.VectorWeightedResponseJets

@[expose] public section

/-! Genuine bounds and spatial Lipschitz control of a linear backward
generator, derived from the actual first three spatial jets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ContDiff Topology BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxHeartbeats 1000000
variable {n : ℕ}

def vectorLinearBackwardGenerator (R U : Field n → ℝ) (m : ℝ) (x : Field n) : ℝ :=
  vectorBilinearTrace (vectorHessian R x)/2+fderiv ℝ R x (m • gradient U x)

theorem norm_vectorBackward_gradient_eq_fderiv (U : Field n → ℝ) (x : Field n) :
    ‖gradient U x‖=‖fderiv ℝ U x‖ := (InnerProductSpace.toDual ℝ (Field n)).symm.norm_map _

theorem vectorBilinearTrace_bound {R : Field n → ℝ} {x : Field n} {A : ℝ}
    (hA : ‖iteratedFDeriv ℝ 2 R x‖ ≤ A) :
    |vectorBilinearTrace (vectorHessian R x)| ≤ (n : ℝ)*A := by
  have hh : ‖vectorHessian R x‖ ≤ A := by rw [vectorHessian_norm_eq];exact hA
  calc
    _ ≤ ∑ i : Fin n,|vectorHessian R x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin n,A := Finset.sum_le_sum (fun i _=>by
      simpa only [PiLp.norm_single,norm_one,mul_one] using
        vectorHessian_apply_bound hh (EuclideanSpace.single i 1) (EuclideanSpace.single i 1))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

theorem vectorLinearBackwardGenerator_bound (R U : Field n → ℝ) (m A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hR : ∀ j,1 ≤ j → j ≤ 3 → ∀ x,‖iteratedFDeriv ℝ j R x‖ ≤ A^j)
    (hU : ∀ j,1 ≤ j → j ≤ 3 → ∀ x,‖iteratedFDeriv ℝ j U x‖ ≤ B^j)
    (x : Field n) :
    ‖vectorLinearBackwardGenerator R U m x‖ ≤ (n : ℝ)*A^2/2+|m| * A*B := by
  have hr : ‖fderiv ℝ R x‖ ≤ A := by simpa only [norm_iteratedFDeriv_one,pow_one] using hR 1 le_rfl (by omega) x
  have hu : ‖gradient U x‖ ≤ B := by
    rw [norm_vectorBackward_gradient_eq_fderiv]
    simpa only [norm_iteratedFDeriv_one,pow_one] using hU 1 le_rfl (by omega) x
  have ht := vectorBilinearTrace_bound (hR 2 (by omega) (by omega) x)
  have hd := (fderiv ℝ R x).le_opNorm (m • gradient U x)
  rw [norm_smul,Real.norm_eq_abs] at hd
  have hd' : ‖fderiv ℝ R x (m • gradient U x)‖ ≤ |m| * A*B := by
    exact hd.trans (by
      have hh := mul_le_mul hr (mul_le_mul_of_nonneg_left hu (abs_nonneg m))
        (mul_nonneg (abs_nonneg m) (norm_nonneg _)) hA
      simpa only [Real.norm_eq_abs,mul_assoc,mul_left_comm,mul_comm] using hh)
  have ht' : ‖vectorBilinearTrace (vectorHessian R x)/2‖ ≤ (n : ℝ)*A^2/2 := by
    simpa only [norm_div,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2)] using
      div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ)≤2)
  exact (norm_add_le _ _).trans (add_le_add ht' hd')

theorem vectorLinearBackwardGenerator_lipschitz (R U : Field n → ℝ)
    (hR : ContDiff ℝ 3 R) (hU : ContDiff ℝ 3 U) (m A B : ℝ)
    (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hRj : ∀ j,1 ≤ j → j ≤ 3 → ∀ x,‖iteratedFDeriv ℝ j R x‖ ≤ A^j)
    (hUj : ∀ j,1 ≤ j → j ≤ 3 → ∀ x,‖iteratedFDeriv ℝ j U x‖ ≤ B^j) :
    LipschitzWith ((n : ℝ)*A^3/2+|m| * (A^2*B+A*B^2)).toNNReal
      (vectorLinearBackwardGenerator R U m) := by
  have hA0 := zero_le_one.trans hA
  have hB0 := zero_le_one.trans hB
  have hlR := lipschitzWith_fderiv_of_jet_bound R (hR.of_le (by norm_num)) (A^2)
    (sq_nonneg _) (hRj 2 (by omega) (by omega))
  have hlU := lipschitzWith_fderiv_of_jet_bound U (hU.of_le (by norm_num)) (B^2)
    (sq_nonneg _) (hUj 2 (by omega) (by omega))
  have ht := finiteGaussianGenerator_lipschitz R hR (fun i : Fin n=>EuclideanSpace.single i 1)
    (fun _=>by simp) A hA hRj 0
  have htE : finiteGaussianGenerator R (fun i : Fin n=>EuclideanSpace.single i 1) 0=
      fun x=>vectorBilinearTrace (vectorHessian R x) := by
    funext x
    simp only [finiteGaussianGenerator,zero_mul,add_zero,vectorBilinearTrace,vectorHessian]
  rw [htE] at ht
  have hr (x : Field n) : ‖fderiv ℝ R x‖ ≤ A := by simpa only [norm_iteratedFDeriv_one,pow_one] using hRj 1 le_rfl (by omega) x
  have hu (x : Field n) : ‖gradient U x‖ ≤ B := by
    rw [norm_vectorBackward_gradient_eq_fderiv]
    simpa only [norm_iteratedFDeriv_one,pow_one] using hUj 1 le_rfl (by omega) x
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity)]
  have hgR : ‖fderiv ℝ R x-fderiv ℝ R y‖ ≤ A^2*dist x y := by
    simpa only [dist_eq_norm,Real.coe_toNNReal _ (sq_nonneg _)] using hlR.dist_le_mul x y
  have hgU : ‖gradient U x-gradient U y‖ ≤ B^2*dist x y := by
    have he : gradient U x-gradient U y=(InnerProductSpace.toDual ℝ (Field n)).symm
      (fderiv ℝ U x-fderiv ℝ U y) := by rw [map_sub];rfl
    rw [he,LinearIsometryEquiv.norm_map]
    simpa only [dist_eq_norm,Real.coe_toNNReal _ (sq_nonneg _)] using hlU.dist_le_mul x y
  have hp : |fderiv ℝ R x (m • gradient U x)-fderiv ℝ R y (m • gradient U y)| ≤
      |m| * (A^2*B+A*B^2)*dist x y := by
    have he : fderiv ℝ R x (m • gradient U x)-fderiv ℝ R y (m • gradient U y)=
        m*((fderiv ℝ R x-fderiv ℝ R y) (gradient U x)+
          fderiv ℝ R y (gradient U x-gradient U y)) := by
      simp only [map_smul,smul_eq_mul,ContinuousLinearMap.sub_apply,map_sub]
      ring
    rw [he,abs_mul]
    have h₁ := ((fderiv ℝ R x-fderiv ℝ R y).le_opNorm (gradient U x)).trans
      (mul_le_mul hgR (hu x) (norm_nonneg _) (by positivity))
    have h₂ := ((fderiv ℝ R y).le_opNorm (gradient U x-gradient U y)).trans
      (mul_le_mul (hr y) hgU (norm_nonneg _) hA0)
    have hh := (abs_add_le _ _).trans (add_le_add
      (by simpa only [Real.norm_eq_abs] using h₁) (by simpa only [Real.norm_eq_abs] using h₂))
    have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg m)
    convert hm using 1 <;> ring
  have htrace : |vectorBilinearTrace (vectorHessian R x)-vectorBilinearTrace (vectorHessian R y)| ≤
      (n : ℝ)*A^3*dist x y := by
    simp only [abs_zero,mul_zero,zero_mul,add_zero,Fintype.card_fin] at ht
    have hh := ht.dist_le_mul x y
    rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity)] at hh
    exact hh
  calc
    _ ≤ |(vectorBilinearTrace (vectorHessian R x)-vectorBilinearTrace (vectorHessian R y))/2|+
        |fderiv ℝ R x (m • gradient U x)-fderiv ℝ R y (m • gradient U y)| := by
      convert abs_add_le ((vectorBilinearTrace (vectorHessian R x)-vectorBilinearTrace (vectorHessian R y))/2)
        (fderiv ℝ R x (m • gradient U x)-fderiv ℝ R y (m • gradient U y)) using 1
      unfold vectorLinearBackwardGenerator
      ring
    _ ≤ ((n : ℝ)*A^3*dist x y)/2+|m| * (A^2*B+A*B^2)*dist x y := by
      rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ)<2)]
      exact add_le_add (div_le_div_of_nonneg_right htrace (by norm_num)) hp
    _ = _ := by ring

end QuantitativePaper
