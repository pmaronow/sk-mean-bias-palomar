module
public import QuantitativeFollowup.ConcentratingPhysicalBounds
public import FourPapersCommon.SquaredResponseEnvelope

@[expose] public section

/-! A uniform response envelope on an arbitrary interior interval, for
the genuine quartic bump and the actual finite-dimensional Parisi law. -/
noncomputable section
open Set MeasureTheory Paper QuantitativePaper FourPapersCommon
open scoped ENNReal
namespace HexagonPaper
open QuantitativeFollowup
set_option maxHeartbeats 2400000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def localDeficitResponseCurvature (beta rho A ell d : ℝ) : ℝ :=
  rho*A^2/72*min ((4*ell/15)^2/(beta*512/(105*ell))) ((4*ell/15)/d)

theorem local_deficit_concentrating_response_envelope (hn : 0 < n)
    (μ ν : Paper.ParisiMeasure) (beta lam rho theta a ell A d : ℝ)
    (hbeta : 0 < beta) (hrho : 0 < rho) (hell : 0 < ell)
    (ha : 0 ≤ a) (he : a+ell ≤ 1) (hA : 0 ≤ A) (hd : 0 < d)
    (hdelta : 4*ell/15 ≤ vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
      beta (1-rho) (lam/beta) (by linarith) a ell)
    (hdensity : ENNReal.ofReal beta •
      (parisiCDFPrimitive (parisiMix μ ν theta)).measure.restrict (Ioo a (a+ell)) ≤
      ENNReal.ofReal d • volume.restrict (Ioo a (a+ell)))
    (hsignal : ∀x∈Ioo a (a+ell), A/2 ≤ beta*(parisiCDF ν x-parisiCDF μ x)) :
    let w := concentratingResponseTest a ell hell ha he
    let Δ := vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
      beta (1-rho) (lam/beta) (by linarith) a ell
    let Y := beta*512/(105*ell)+2*d*Δ
    0 < Y ∧ responseC1EnergyDenominator (n:=n) μ ν beta (1-rho) lam theta
      (by linarith) w ≤ Y ∧
      localDeficitResponseCurvature beta rho A ell d*Y ≤
        rho^3*(responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith) w)^2 := by
  dsimp only
  let w := concentratingResponseTest a ell hell ha he
  let Δ := vectorConcentratingDelta (n:=n) (parisiMix μ ν theta)
    beta (1-rho) (lam/beta) (by linarith) a ell
  let S := responseC1Signal (n:=n) μ ν beta (1-rho) lam theta (by linarith) w
  have hB : 0 < beta*512/(105*ell) := by positivity
  have hSign := concentrating_physical_signal_lower (n:=n) μ ν (parisiMix μ ν theta)
    beta (1-rho) lam a ell (A/2) (by linarith) hell ha he hsignal
  have hSign' : A*Δ/2 ≤ rho*S := by
    convert hSign using 1
    · dsimp only [Δ]; ring
    · dsimp only [S,responseC1Signal,w,concentratingResponseTest]
      congr 1
      ring
  have hEnvelope := squared_response_upper_envelope rho A (4*ell/15) Δ S
    (beta*512/(105*ell)) d hrho hA (by positivity) hdelta hB hd hSign'
  have hDen := concentrating_response_denominator_bound hn μ ν beta (1-rho) lam theta
    a ell d hbeta (by linarith) hell ha he hd.le hdensity
  exact ⟨hEnvelope.1,hDen,hEnvelope.2⟩

theorem local_deficit_response_curvature_eq (beta rho A ell d : ℝ)
    (hbeta : 0 < beta) (hell : 0 < ell) :
    localDeficitResponseCurvature beta rho A ell d =
      rho*A^2/72*min (7*ell^3/(480*beta)) (4*ell/(15*d)) := by
  unfold localDeficitResponseCurvature
  congr 1
  apply congrArg₂ min
  · field_simp
    ring
  · ring

end HexagonPaper
