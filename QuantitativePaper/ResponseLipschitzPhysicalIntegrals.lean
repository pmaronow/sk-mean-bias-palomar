module
public import QuantitativePaper.ResponsePhysicalIntegrals
public import QuantitativePaper.ResponseLipschitzTest

@[expose] public section
noncomputable section
open MeasureTheory
namespace QuantitativePaper
variable {n : ℕ}

theorem intervalIntegrable_response_Lipschitz_signal (μ ν ρ : Paper.ParisiMeasure)
    (β t lam : ℝ) (w : ResponseLipschitzTest) (a b : ℝ) (ht : t<1) :
    IntervalIntegrable (fun q=>β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q)*w.value q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q) volume a b:=by
  have hc : Continuous (fun q=>w.value q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q):=
    w.continuous.mul (continuous_responseAveragedCurvatureReal (n:=n) ρ β t lam ht)
  have hi:=((Paper.parisiCDF_intervalIntegrable ν a b).sub
    (Paper.parisiCDF_intervalIntegrable μ a b)).continuousOn_mul hc.continuousOn
  convert hi.const_mul β using 1
  funext q
  ring

theorem intervalIntegrable_response_Lipschitz_mean (μ : Paper.ParisiMeasure)
    (β t lam : ℝ) (w : ResponseLipschitzTest) (a b : ℝ) (ht : t≤1) :
    IntervalIntegrable (fun q=>(w.slope q)^2*responseMeanHessianReal (n:=n) μ β t lam ht q)
      volume a b:=
  intervalIntegrable_responseLipschitzSlope_sq_mul w a b _
    ((continuous_responseMeanHessianReal μ β t lam ht).intervalIntegrable a b)
end QuantitativePaper
