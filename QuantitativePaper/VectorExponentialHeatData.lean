module
public import QuantitativePaper.GaussianWeightedJets
public import FourPapersCommon.VectorDriftTaylor

@[expose] public section

/-! Analytic exponential-growth data for genuine vector Gaussian heat
integrals. Exponentially weighted bounded observables satisfy the data from
their actual jets and the potential's field Lipschitz bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open FourPapersCommon
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
variable {n : ℕ}

structure VectorHeatDatum (F : Field n → ℝ) where
  regularity : ContDiff ℝ 2 F
  growthBound : ℝ≥0
  rate : ℝ≥0
  value_bound : ∀ x,‖F x‖ ≤ growthBound*Real.exp (rate*‖x‖)
  first_bound : ∀ x,‖fderiv ℝ F x‖ ≤ growthBound*Real.exp (rate*‖x‖)
  second_bound : ∀ x,‖vectorHessian F x‖ ≤ growthBound*Real.exp (rate*‖x‖)

theorem integrable_field_norm_mul_exp (c : ℝ) :
    Integrable (fun z : Field n=>‖z‖*Real.exp (c*‖z‖)) (fieldGaussian n) := by
  apply (SYK.integrable_exp_mul_norm (ι := Fin n) (c+1)).mono'
    ((continuous_norm.mul (Real.continuous_exp.comp (continuous_const.mul continuous_norm))).aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  change ‖‖z‖*Real.exp (c*‖z‖)‖ ≤ Real.exp ((c+1)*‖z‖)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),add_mul,
    one_mul,Real.exp_add]
  have hh : ‖z‖ ≤ Real.exp ‖z‖ := (by linarith : ‖z‖ ≤ ‖z‖+1).trans (Real.add_one_le_exp _)
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hh (Real.exp_pos (c*‖z‖)).le

theorem VectorHeatDatum.integrable_shift {F : Field n → ℝ} (d : VectorHeatDatum F)
    (v : ℝ) (x : Field n) : Integrable (fun z=>F (fieldShift v x z)) (fieldGaussian n) := by
  apply ((SYK.integrable_exp_mul_norm (ι := Fin n) (d.rate*Real.sqrt v)).const_mul
    (d.growthBound*Real.exp (d.rate*‖x‖))).mono'
      ((d.regularity.continuous.comp (by unfold fieldShift;fun_prop)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro z
  have hn : ‖fieldShift v x z‖ ≤ ‖x‖+Real.sqrt v*‖z‖ := by
    simpa only [fieldShift,norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)] using norm_add_le x (Real.sqrt v • z)
  apply (d.value_bound _).trans
  calc
    _ ≤ d.growthBound*Real.exp (d.rate*(‖x‖+Real.sqrt v*‖z‖)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hn d.rate.coe_nonneg)) d.growthBound.coe_nonneg
    _ = _ := by rw [mul_add,Real.exp_add];simp only [mul_assoc]

theorem vectorHeatDatum_exp_observable
    (f g : Field n → ℝ) (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (L : ℝ≥0) (hlip : LipschitzWith L f) (m K : ℝ) (hK : 0 ≤ K)
    (G : ℕ → ℝ) (hG : ∀ i,0 ≤ G i)
    (hjets : ∀ i,1 ≤ i → i ≤ 2 → ∀ x,‖iteratedFDeriv ℝ i f x‖ ≤ K^i)
    (hgJets : ∀ i,i ≤ 2 → ∀ x,‖iteratedFDeriv ℝ i g x‖ ≤ G i) :
    Nonempty (VectorHeatDatum (fun x=>Real.exp (m*f x)*g x)) := by
  let P := gaussianWeightedJetCoefficient m K G
  let C := (P 0+P 1+P 2)*Real.exp (|m| * |f 0|)
  have hP (j : ℕ) : 0 ≤ P j := gaussianWeightedJetCoefficient_nonneg m K hK G hG j
  have hC : 0 ≤ C := mul_nonneg (add_nonneg (add_nonneg (hP 0) (hP 1)) (hP 2)) (Real.exp_pos _).le
  have hc (j : ℕ) (hj : j ≤ 2) : P j ≤ P 0+P 1+P 2 := by
    interval_cases j <;> linarith [hP 0,hP 1,hP 2]
  have hb (j : ℕ) (hj : j ≤ 2) (x : Field n) :
      ‖iteratedFDeriv ℝ j (fun y=>Real.exp (m*f y)*g y) x‖ ≤ C*Real.exp ((|m| * L)*‖x‖) := by
    have hf0 : |f x| ≤ |f 0|+(L : ℝ)*‖x‖ := by
      have hh := hlip.dist_le_mul x 0
      simp only [Real.dist_eq,dist_zero_right] at hh
      have ha := abs_add_le (f 0) (f x-f 0)
      rw [add_sub_cancel] at ha
      exact ha.trans (add_le_add (le_refl _) hh)
    have hexp : Real.exp (m*f x) ≤ Real.exp (|m| * |f 0|)*Real.exp ((|m| * L)*‖x‖) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm := le_abs_self (m*f x)
      rw [abs_mul] at hm
      nlinarith [mul_le_mul_of_nonneg_left hf0 (abs_nonneg m)]
    apply (norm_iteratedFDeriv_exp_mul_observable_le f g hf hg m K hK G hG hjets hgJets hj x).trans
    change P j*Real.exp (m*f x) ≤ _
    have hh := mul_le_mul (hc j hj) hexp (Real.exp_pos _).le
      (add_nonneg (add_nonneg (hP 0) (hP 1)) (hP 2))
    simpa only [C,mul_assoc] using hh
  refine ⟨{
    regularity := ((contDiff_const.mul hf).exp).mul hg
    growthBound := ⟨C,hC⟩
    rate := ⟨|m| * L,mul_nonneg (abs_nonneg _) L.coe_nonneg⟩
    value_bound := fun x=>by
      change ‖Real.exp (m*f x)*g x‖ ≤ C*Real.exp ((|m| * L)*‖x‖)
      simpa only [norm_iteratedFDeriv_zero] using hb 0 (by omega) x
    first_bound := fun x=>by
      change ‖fderiv ℝ (fun y=>Real.exp (m*f y)*g y) x‖ ≤ C*Real.exp ((|m| * L)*‖x‖)
      rw [← norm_iteratedFDeriv_one];exact hb 1 (by omega) x
    second_bound := fun x=>by
      change ‖vectorHessian (fun y=>Real.exp (m*f y)*g y) x‖ ≤ C*Real.exp ((|m| * L)*‖x‖)
      rw [vectorHessian_norm_eq];exact hb 2 le_rfl x
  }⟩

end QuantitativePaper
