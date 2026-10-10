module
public import QuantitativePaper.ResponseMeanUpper
public import QuantitativePaper.ResponseTentEnergyIntegrable
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! Continuous real-time extensions of the actual physical responses and
genuine integrability of their time and Stieltjes tent tests. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

def responseMeanHessianReal (μ : Paper.ParisiMeasure) (β t lam : ℝ) (ht : t≤1)
    (q : ℝ) : ℝ:=responseMeanHessian (n:=n) μ β t lam ht (projIcc 0 1 zero_le_one q)

def responseAveragedCurvatureReal (μ : Paper.ParisiMeasure) (β t lam : ℝ) (ht : t≤1)
    (q : ℝ) : ℝ:=responseAveragedCurvature (n:=n) μ β t lam ht (projIcc 0 1 zero_le_one q)

theorem continuous_responseAveragedCurvature (μ : Paper.ParisiMeasure) (β t lam : ℝ)
    (ht : t<1) : Continuous (responseAveragedCurvature (n:=n) μ β t lam ht.le):=by
  have he : responseAveragedCurvature (n:=n) μ β t lam ht.le=
      fun q=>vectorMeanOverlapDerivative (n:=n) μ β t (lam/β) ht.le q/(1-t):=by
    funext q
    rw [vectorMeanOverlapDerivative_eq_responseCurvature]
    exact (mul_div_cancel_left₀ _ (by linarith : (1-t)≠0)).symm
  rw [he]
  exact (continuous_vectorMeanOverlapDerivative μ β t (lam/β) ht.le).div_const _

theorem continuous_responseMeanHessianReal (μ : Paper.ParisiMeasure) (β t lam : ℝ)
    (ht : t≤1) : Continuous (responseMeanHessianReal (n:=n) μ β t lam ht):=
  (continuous_responseMeanHessian μ β t lam ht).comp continuous_projIcc

theorem continuous_responseAveragedCurvatureReal (μ : Paper.ParisiMeasure) (β t lam : ℝ)
    (ht : t<1) : Continuous (responseAveragedCurvatureReal (n:=n) μ β t lam ht.le):=
  (continuous_responseAveragedCurvature μ β t lam ht).comp continuous_projIcc

theorem intervalIntegrable_response_tent_signal (μ ν ρ : Paper.ParisiMeasure)
    (β t lam ell a b : ℝ) (ht : t<1) :
    IntervalIntegrable (fun q=>β*(Paper.parisiCDF ν q-Paper.parisiCDF μ q)*responseTent ell q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q) volume a b:=by
  have hc : Continuous (fun q=>responseTent ell q*
      responseAveragedCurvatureReal (n:=n) ρ β t lam ht.le q):=
    (continuous_responseTent ell).mul
      (continuous_responseAveragedCurvatureReal (n:=n) ρ β t lam ht)
  have hi:=((Paper.parisiCDF_intervalIntegrable ν a b).sub
    (Paper.parisiCDF_intervalIntegrable μ a b)).continuousOn_mul hc.continuousOn
  convert hi.const_mul β using 1
  funext q
  ring

theorem intervalIntegrable_response_tent_mean (μ : Paper.ParisiMeasure)
    (β t lam ell a b : ℝ) (ht : t≤1) :
    IntervalIntegrable (fun q=>(responseTentSlope ell q)^2*
      responseMeanHessianReal (n:=n) μ β t lam ht q) volume a b:=
  intervalIntegrable_responseTentSlope_sq_mul ell a b _
    ((continuous_responseMeanHessianReal μ β t lam ht).intervalIntegrable a b)

end QuantitativePaper
