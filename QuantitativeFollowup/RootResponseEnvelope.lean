module
public import QuantitativeFollowup.ConcentratingPhysicalBounds
public import FourPapersCommon.SquaredResponseEnvelope

@[expose] public section

/-! Actual root signal/denominator envelopes for the C¹ response. This
module reduces the constructed concentrating segment to the literal
curvature constant; it does not assume a functional second derivative. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace QuantitativeFollowup
set_option maxHeartbeats 2200000
variable {n : ℕ}

def rootResponseCurvature (beta rho k q d : ℝ) : ℝ :=
  rho*k^2*q^2/4608*min (7*q^3/(3840*beta)) (2*q/(15*d))

theorem root_concentrating_response_envelope (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (beta lam rho theta q k d : ℝ) (hbeta : 0 < beta) (hrho : 0 < rho)
    (hq : q∈Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hd : 0 < d)
    (hdelta : 2*q/15 ≤ vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
      beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2))
    (hdensity : ENNReal.ofReal beta •
      (parisiCDFPrimitive (parisiMix μ ν theta)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo (q/4) (3*q/4)))
    (hsignal : ∀x∈Ioo (q/4) (3*q/4), k*q/16 ≤ beta*(parisiCDF ν x-parisiCDF μ x)) :
    let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
      (by linarith [hq.1]) (by linarith [hq.2])
    let Δ := vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
      beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2)
    let Y := beta*512/(105*(q/2))+2*d*Δ
    0 < Y ∧ responseC1EnergyDenominator (n:=n) μ ν beta (1-rho) lam theta (by linarith) w ≤ Y ∧
      rootResponseCurvature beta rho k q d*Y ≤
        rho^3*(responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith) w)^2 := by
  dsimp only
  let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2])
  let Δ := vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
    beta (1-rho) (lam/beta) (by linarith) (q/4) (q/2)
  let S := responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith) w
  have hEnd : q/4+q/2=3*q/4 := by ring
  have hB : 0 < beta*512/(105*(q/2)) := by positivity [hq.1]
  have hSign := concentrating_physical_signal_lower (n:=n) μ ν (parisiMix μ ν theta)
    beta (1-rho) lam (q/4) (q/2) (k*q/16) (by linarith) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2]) (by simpa only [hEnd] using hsignal)
  have hSign' : (k*q/8)*Δ/2 ≤ rho*S := by
    convert hSign using 1
    · dsimp only [Δ]
      ring
    · dsimp only [S,responseC1Signal,w,concentratingResponseTest]
      congr 1
      ring
  have hEnvelope := squared_response_upper_envelope rho (k*q/8) (2*q/15) Δ S
    (beta*512/(105*(q/2))) d hrho (by positivity [hq.1]) (by positivity [hq.1])
    hdelta hB hd hSign'
  have hDen := concentrating_response_denominator_bound hn μ ν beta (1-rho) lam theta
    (q/4) (q/2) d hbeta (by linarith) (half_pos hq.1) (by linarith [hq.1])
    (by linarith [hq.2]) hd.le (by simpa only [hEnd] using hdensity)
  refine ⟨hEnvelope.1,hDen,?_⟩
  have hCoeff : rho*(k*q/8)^2/72*min ((2*q/15)^2/(beta*512/(105*(q/2)))) ((2*q/15)/d) =
      rootResponseCurvature beta rho k q d := by
    unfold rootResponseCurvature
    congr 1
    · ring
    · apply congrArg₂ min
      · field_simp
        ring
      · ring
  rw [hCoeff] at hEnvelope
  exact hEnvelope.2

end QuantitativeFollowup
