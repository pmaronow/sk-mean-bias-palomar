module
public import QuantitativePaper.VectorFieldJetTransfer
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

/-! A genuine spatial Lipschitz bound for the finite Gaussian generator,
derived from the first three actual Frechet jets. -/
noncomputable section
open scoped ContDiff NNReal BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 128

theorem lipschitzWith_fderiv_of_jet_bound (f : E→ℝ) (hf : ContDiff ℝ 2 f)
    (K : ℝ) (hK : 0 ≤ K) (hB : ∀x,‖iteratedFDeriv ℝ 2 f x‖ ≤ K) :
    LipschitzWith K.toNNReal (fderiv ℝ f) := by
  have hd : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  apply lipschitzWith_of_nnnorm_fderiv_le (hd.differentiable (by norm_num))
  intro x
  rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ hK,
    ←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv]
  exact hB x

theorem lipschitzWith_second_fderiv_of_jet_bound (f : E→ℝ) (hf : ContDiff ℝ 3 f)
    (K : ℝ) (hK : 0 ≤ K) (hB : ∀x,‖iteratedFDeriv ℝ 3 f x‖ ≤ K) :
    LipschitzWith K.toNNReal (fderiv ℝ (fderiv ℝ f)) := by
  have h₁ : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ f)) := h₁.fderiv_right (by norm_num)
  apply lipschitzWith_of_nnnorm_fderiv_le (h₂.differentiable (by norm_num))
  intro x
  rw [←NNReal.coe_le_coe,coe_nnnorm,Real.coe_toNNReal _ hK,
    ←norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv,norm_iteratedFDeriv_fderiv]
  exact hB x

def finiteGaussianGenerator {ι : Type*} [Fintype ι] (f : E→ℝ) (w : ι→E) (m : ℝ) (x : E) : ℝ :=
  ∑i,(fderiv ℝ (fderiv ℝ f) x (w i) (w i)+m*(fderiv ℝ f x (w i))^2)

theorem finiteGaussianGenerator_lipschitz {ι : Type*} [Fintype ι]
    (f : E→ℝ) (hf : ContDiff ℝ 3 f) (w : ι→E) (hw : ∀i,‖w i‖ ≤ 1)
    (K : ℝ) (hK : 1 ≤ K)
    (hB : ∀j,1 ≤ j → j ≤ 3 → ∀x,‖iteratedFDeriv ℝ j f x‖ ≤ K^j) (m : ℝ) :
    LipschitzWith ((Fintype.card ι : ℝ)*(K^3+2*|m| * K^3)).toNNReal
      (finiteGaussianGenerator f w m) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have h₁ := lipschitzWith_fderiv_of_jet_bound f (hf.of_le (by norm_num)) (K^2)
    (pow_nonneg hK0 _) (hB 2 (by omega) (by omega))
  have h₂ := lipschitzWith_second_fderiv_of_jet_bound f hf (K^3)
    (pow_nonneg hK0 _) (hB 3 (by omega) le_rfl)
  have hb (x : E) (i : ι) : |fderiv ℝ f x (w i)| ≤ K := by
    have hh := (fderiv ℝ f x).le_opNorm (w i)
    rw [Real.norm_eq_abs] at hh
    have hd : ‖fderiv ℝ f x‖ ≤ K := by simpa only [norm_iteratedFDeriv_one,pow_one] using hB 1 le_rfl (by omega) x
    exact hh.trans ((mul_le_mul hd (hw i) (norm_nonneg _) hK0).trans_eq (mul_one _))
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq,Real.coe_toNNReal _ (by positivity),finiteGaussianGenerator,finiteGaussianGenerator,
    ←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑i,|fderiv ℝ (fderiv ℝ f) x (w i) (w i)+m*(fderiv ℝ f x (w i))^2-
      (fderiv ℝ (fderiv ℝ f) y (w i) (w i)+m*(fderiv ℝ f y (w i))^2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_ : ι,(K^3+2*|m| * K^3)*dist x y := by
      apply Finset.sum_le_sum
      intro i hi
      have hg : |fderiv ℝ f x (w i)-fderiv ℝ f y (w i)| ≤ K^2*dist x y := by
        have hh := (fderiv ℝ f x-fderiv ℝ f y).le_opNorm (w i)
        simp only [ContinuousLinearMap.sub_apply,Real.norm_eq_abs] at hh
        have hd := h₁.dist_le_mul x y
        rw [dist_eq_norm,Real.coe_toNNReal _ (pow_nonneg hK0 _)] at hd
        exact hh.trans ((mul_le_mul hd (hw i) (norm_nonneg _) (by positivity)).trans_eq (mul_one _))
      have hH : |fderiv ℝ (fderiv ℝ f) x (w i) (w i)-
          fderiv ℝ (fderiv ℝ f) y (w i) (w i)| ≤ K^3*dist x y := by
        have h₀ := ((fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y) (w i)).le_opNorm (w i)
        simp only [ContinuousLinearMap.sub_apply,Real.norm_eq_abs] at h₀
        have h₃ := (fderiv ℝ (fderiv ℝ f) x-fderiv ℝ (fderiv ℝ f) y).le_opNorm (w i)
        have hd := h₂.dist_le_mul x y
        rw [dist_eq_norm,Real.coe_toNNReal _ (pow_nonneg hK0 _)] at hd
        have hm := (mul_le_mul_of_nonneg_right h₃ (norm_nonneg (w i)))
        have hl := mul_le_mul hd (hw i) (norm_nonneg _) (by positivity)
        have hl' := mul_le_mul_of_nonneg_right hl (norm_nonneg (w i))
        have hl'' := mul_le_mul_of_nonneg_left (hw i) (by positivity : 0 ≤ K^3*dist x y*1)
        exact h₀.trans (hm.trans (hl'.trans (by simpa only [mul_one] using hl'')))
      have hs : |(fderiv ℝ f x (w i))^2-(fderiv ℝ f y (w i))^2| ≤ 2*K^3*dist x y := by
        rw [sq_sub_sq,abs_mul]
        have ha := (abs_add_le (fderiv ℝ f x (w i)) (fderiv ℝ f y (w i))).trans
          (add_le_add (hb x i) (hb y i))
        have hh := mul_le_mul hg ha (abs_nonneg _) (by positivity)
        convert hh using 1 <;> ring
      calc
        _ ≤ |fderiv ℝ (fderiv ℝ f) x (w i) (w i)-fderiv ℝ (fderiv ℝ f) y (w i) (w i)|+
          |m| * |(fderiv ℝ f x (w i))^2-(fderiv ℝ f y (w i))^2| := by
          convert abs_add_le (fderiv ℝ (fderiv ℝ f) x (w i) (w i)-fderiv ℝ (fderiv ℝ f) y (w i) (w i))
            (m*((fderiv ℝ f x (w i))^2-(fderiv ℝ f y (w i))^2)) using 1
          · congr 1
            ring
          · rw [abs_mul]
        _ ≤ K^3*dist x y+|m| * (2*K^3*dist x y) :=
          add_le_add hH (mul_le_mul_of_nonneg_left hs (abs_nonneg m))
        _ = _ := by ring
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul];ring

end QuantitativePaper
