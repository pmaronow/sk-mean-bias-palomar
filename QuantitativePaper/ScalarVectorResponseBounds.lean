module
public import QuantitativePaper.ScalarVectorSpatialIdentification

@[expose] public section

/-! Pointwise scalar smoothing bounds control the actual one-spin physical
response means under every normalized outer law. No state-law substitution
is needed, since the scalar bound holds at every spatial point. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
open scoped BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem responseHessianTrace_one_zero_time (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample 1) :
    responseHessianTrace μ β 0 (by norm_num) q sample=
      β*parisiHessian β μ (q,vectorMeasureState μ β 0 (by norm_num) (q:ℝ).toNNReal sample 0) := by
  simp only [responseHessianTrace,Matrix.trace,Matrix.diag,vectorMeasureHessianMatrix,
    Fin.sum_univ_one]
  rw [vectorMeasureHessian_one_zero_time μ β hβ]

theorem vectorMeasureHessianEnergy_one_zero_time (μ : Paper.ParisiMeasure)
    (β : ℝ) (hβ : β≠0) (q : Paper.Overlap) (sample : VectorDisorderBrownianSample 1) :
    vectorMeasureHessianEnergy μ β 0 (by norm_num) q sample=
      (parisiHessian β μ (q,vectorMeasureState μ β 0 (by norm_num) (q:ℝ).toNNReal sample 0))^2 := by
  simp only [vectorMeasureHessianEnergy,vectorHessianHilbertSquare,Fin.sum_univ_one,
    EuclideanSpace.real_norm_sq_eq]
  rw [vectorMeasureHessian_one_zero_time μ β hβ]

theorem responseMeanHessian_one_zero_time_le (μ : Paper.ParisiMeasure)
    (β lam C : ℝ) (hβ : 0<β) (q : Paper.Overlap)
    (hBound : ∀x:ℝ,β*parisiHessian β μ (q,x)≤C) :
    responseMeanHessian (n:=1) μ β 0 lam (by norm_num) q≤C := by
  haveI:=vectorMeasureDisorderTilt_probability (n:=1) μ β 0 (lam/β) (by norm_num)
  have hi:=(memLp_responseHessianTrace (n:=1) μ β 0 lam (by norm_num) q).integrable
    (by norm_num)
  have hh:=integral_mono hi (integrable_const C) (fun sample=>by
    rw [responseHessianTrace_one_zero_time μ β hβ.ne']
    exact hBound _)
  simpa only [responseMeanHessian,Nat.cast_one,one_div,inv_one,one_mul,integral_const,
    probReal_univ,one_smul] using hh

theorem responseAveragedCurvature_one_zero_time_le (μ : Paper.ParisiMeasure)
    (β lam C : ℝ) (hβ : 0<β) (q : Paper.Overlap)
    (hBound : ∀x:ℝ,β*parisiHessian β μ (q,x)≤C) :
    responseAveragedCurvature (n:=1) μ β 0 lam (by norm_num) q≤C^2 := by
  haveI:=vectorMeasureDisorderTilt_probability (n:=1) μ β 0 (lam/β) (by norm_num)
  have hi:=(integrable_vectorMeasureHessianEnergy (n:=1) μ β 0 (lam/β) (by norm_num) q).const_mul (β^2)
  have hh:=integral_mono hi (integrable_const (C^2)) (fun sample=>by
    rw [vectorMeasureHessianEnergy_one_zero_time μ β hβ.ne',←mul_pow]
    apply pow_le_pow_left₀ _ (hBound _) 2
    exact mul_nonneg hβ.le (parisiHessian_pos_all β μ q _ q.property).le)
  rw [integral_const_mul] at hh
  simpa only [responseAveragedCurvature,Nat.cast_one,div_one,integral_const,
    probReal_univ,one_smul] using hh

end QuantitativePaper
