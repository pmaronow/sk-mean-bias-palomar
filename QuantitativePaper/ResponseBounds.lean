module
public import QuantitativePaper.ResponsePhysicalIntegrals

@[expose] public section
noncomputable section
open MeasureTheory
namespace QuantitativePaper
variable {n : ℕ}

theorem norm_responseMeanHessian_le (μ : Paper.ParisiMeasure) (β t lam : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    ‖responseMeanHessian (n:=n) μ β t lam ht q‖≤|1/(n:ℝ)| *(|β| *(n:ℝ)^2):=by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t (lam/β) ht
  unfold responseMeanHessian
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hh:=norm_integral_le_of_norm_le_const
    (μ:=vectorMeasureDisorderTilt (n:=n) μ β t (lam/β))
    (f:=responseHessianTrace (n:=n) μ β t ht q) (C:=|β| *(n:ℝ)^2)
    (.of_forall fun sample=>by simpa only [Real.norm_eq_abs] using abs_responseHessianTrace_le μ β t ht q sample)
  simpa only [probReal_univ,mul_one] using hh

theorem norm_responseAveragedCurvature_le (μ : Paper.ParisiMeasure) (β t lam : ℝ)
    (ht : t≤1) (q : Paper.Overlap) :
    ‖responseAveragedCurvature (n:=n) μ β t lam ht q‖≤|β^2/(n:ℝ)| *(n:ℝ)^3:=by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t (lam/β) ht
  unfold responseAveragedCurvature
  rw [norm_mul,Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hh:=norm_integral_le_of_norm_le_const
    (μ:=vectorMeasureDisorderTilt (n:=n) μ β t (lam/β))
    (f:=vectorMeasureHessianEnergy (n:=n) μ β t ht q) (C:=(n:ℝ)^3)
    (.of_forall fun sample=>by
      rw [Real.norm_eq_abs,abs_of_nonneg (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).1]
      exact (vectorMeasureHessianEnergy_nonneg_le μ β t ht q sample).2)
  simpa only [probReal_univ,mul_one] using hh

end QuantitativePaper
