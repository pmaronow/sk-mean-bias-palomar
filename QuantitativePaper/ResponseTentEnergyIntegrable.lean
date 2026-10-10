module
public import QuantitativePaper.ResponseTentProductIntegrable

@[expose] public section

noncomputable section
open MeasureTheory
namespace QuantitativePaper

theorem intervalIntegrable_responseTentSlope_sq_mul (ell a b : ℝ) (R : ℝ→ℝ)
    (hR : IntervalIntegrable R volume a b) :
    IntervalIntegrable (fun q=>(responseTentSlope ell q)^2*R q) volume a b:=by
  rw [intervalIntegrable_iff] at hR ⊢
  apply hR.bdd_mul ((measurable_responseTentSlope ell).pow_const 2).aestronglyMeasurable
  exact .of_forall fun q=>by
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_responseTentSlope_le ell q) 2

end QuantitativePaper
