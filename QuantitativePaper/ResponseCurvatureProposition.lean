module
public import QuantitativePaper.ResponseCurvatureLower
public import QuantitativePaper.ResponseMeanUpper

@[expose] public section

/-! Literal Appendix Lemma A.1 for the actual energy-scale response model.
The root-floor condition is precisely admissibility of the profile with
its retained outer tilt; all analytic and stochastic conclusions are proved. -/
noncomputable section
open Set Paper
namespace QuantitativePaper

def ResponseCurvatureTarget : Prop :=
  ∀n : ℕ,0 < n → ∀μ : ParisiMeasure,∀β t lam : ℝ,
    0 < β → ∀ht : t ∈ Ico 0 1,0 ≤ lam → lam ≤ β*parisiCDF μ 0 →
    Antitone (responseMeanHessian (n:=n) μ β t lam ht.2.le) ∧
      (∀q : Overlap,0 < (q : ℝ) →
        responseMeanHessian (n:=n) μ β t lam ht.2.le q ≤ 1/Real.sqrt ((1-t)*(q : ℝ))) ∧
      (∀_hβ : 1 ≤ β,∀U : ℝ,0 ≤ U → ∀q : Overlap,(q : ℝ) < 1 →
        β*parisiCDF μ q ≤ U → (responseCurvatureConstant U)^2 ≤
          responseAveragedCurvature (n:=n) μ β t lam ht.2.le q)

theorem response_curvature : ResponseCurvatureTarget := by
  intro n hn μ β t lam hβ ht hlam hfloor
  refine ⟨responseMeanHessian_antitone μ β t lam hβ ht.2,?_,?_⟩
  · intro q hq
    exact responseMeanHessian_upper hn μ β t lam hβ ht.2 q hq
  · intro hβ1 U _hU q _hq hU
    exact responseAveragedCurvature_lower hn μ β t lam U hβ1 ht hlam hfloor q hU

end QuantitativePaper
