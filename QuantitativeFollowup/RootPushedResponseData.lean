module
public import QuantitativeFollowup.RootResponseEnvelope
public import QuantitativeFollowup.AffineProfileCurve

@[expose] public section

/-! Actual response data for every genuine pushed affine-CDF segment.
The field-law curvature and ordinary measure density are transported by
proved equality with the probability-measure mix of its endpoints. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2400000
variable {n : ℕ}

theorem root_pushed_response_data (hn : 0 < n)
    (P : ℝ → Paper.ParisiMeasure) (bar : Paper.ParisiMeasure) (psi : ℝ → ℝ)
    (beta lam rho q k d : ℝ) (hbeta : 0 < beta) (hrho : 0 < rho)
    (hq : q∈Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hd : 0 < d)
    (hProfile : ∀theta∈Icc (0 : ℝ) 1, ∀x,
      beta*parisiCDF (P theta) x=beta*parisiCDF bar x+theta*psi x)
    (hContact : ∀theta∈Icc (1/4 : ℝ) (3/4),
      2*q/15 ≤ vectorConcentratingDelta (n:=n) (P theta)
        beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2) ∧
      ENNReal.ofReal beta • (parisiCDFPrimitive (P theta)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
        ENNReal.ofReal d • volume.restrict (Ioo (q/4) (3*q/4)))
    (hsignal : ∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤ psi x) :
    let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
      (by linarith [hq.1]) (by linarith [hq.2])
    ∀theta∈Ioo (1/4 : ℝ) (3/4),
      let Y := beta*512/(105*(q/2))+2*d*vectorConcentratingDelta (n:=n)
        (P theta) beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2)
      0 < Y ∧ responseC1EnergyDenominator (n:=n) (P 0) (P 1) beta (1-rho) lam theta
        (by linarith) w ≤ Y ∧ rootResponseCurvature beta rho k q d*Y ≤
        rho^3*(responseC1Signal (n:=n) (P 0) (P 1) beta (1-rho) lam theta (by linarith) w)^2 := by
  dsimp only
  intro theta htheta
  have ht : theta∈Icc (0 : ℝ) 1 := ⟨by linarith [htheta.1],by linarith [htheta.2]⟩
  have htMid : theta∈Icc (1/4 : ℝ) (3/4) := ⟨htheta.1.le,htheta.2.le⟩
  have hMix : P theta=parisiMix (P 0) (P 1) theta := by
    simpa only [mul_zero,zero_add,mul_one] using
      affine_profile_curve_mix P bar beta 0 1 psi hbeta hProfile 0 1 theta
        (by norm_num) (by norm_num) ht
  have hGap : ∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤ beta*(parisiCDF (P 1) x-parisiCDF (P 0) x) := by
    intro x hx
    have hZero := hProfile 0 (by norm_num) x
    have hOne := hProfile 1 (by norm_num) x
    linarith [hsignal x hx]
  have hh := root_concentrating_response_envelope hn (P 0) (P 1) beta lam rho theta q k d
    hbeta hrho hq hk hd (by simpa only [←hMix] using (hContact theta htMid).1)
    (by simpa only [←hMix] using (hContact theta htMid).2) hGap
  simpa only [←hMix] using hh

end QuantitativeFollowup
