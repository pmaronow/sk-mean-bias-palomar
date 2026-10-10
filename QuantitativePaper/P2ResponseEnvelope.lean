module
public import QuantitativePaper.P2ResponsePhysicalBounds
public import QuantitativePaper.P2MidpointAlgebra
public import QuantitativePaper.ResponseC1Midpoint

@[expose] public section

/-! Actual sharper midpoint response, with local profile and measure data.
No second-variation or midpoint inequality is supplied as a premise. -/
noncomputable section
open Set MeasureTheory Paper QuantitativeFollowup
open scoped ENNReal
namespace QuantitativePaper
set_option maxHeartbeats 1800000
variable {n : ℕ}

theorem p2_concentrating_response_envelope (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam r q k Cs θ : ℝ) (hβ : 1 ≤ β) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hCs : 0 ≤ Cs) (hlam : 0 ≤ lam)
    (hfloor : lam ≤ β*parisiCDF (parisiMix μ ν θ) 0)
    (hprofile : ∀x ∈ Icc (q/4) (3*q/4), β*parisiCDF (parisiMix μ ν θ) x ≤ 2)
    (hdensity : ENNReal.ofReal β •
      (parisiCDFPrimitive (parisiMix μ ν θ)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal (Cs+1/(Real.sqrt r*q*Real.sqrt q)) • volume.restrict (Ioo (q/4) (3*q/4)))
    (hsignal : ∀x ∈ Ioo (q/4) (3*q/4), k*q/8 ≤ β*(parisiCDF ν x-parisiCDF μ x)) :
    let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
      (by linarith [hq.1]) (by linarith [hq.2])
    let Y := (32+2*Cs)/(Real.sqrt r*q*Real.sqrt q)
    0 < Y ∧ responseC1EnergyDenominator (n := n) μ ν β (1-r) lam θ (by linarith [hr.1]) w ≤ Y ∧
      (4*p2MidpointConstant k Cs*r^3*Real.sqrt r*q^5*Real.sqrt q)*Y ≤
        r^3*(responseC1Signal (n := n) μ ν β (1-r) lam θ (by linarith [hr.1]) w)^2 := by
  dsimp only
  let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2])
  let Δ := vectorConcentratingDelta (n := n) (parisiMix μ ν θ) β (1-r) (lam/β)
    (by linarith [hr.1]) (q/4) (q/2)
  let S := responseC1Signal (n := n) μ ν β (1-r) lam θ (by linarith [hr.1]) w
  have hβp : 0 < β := by linarith
  have hE : q/4+q/2 = 3*q/4 := by ring
  have hΔ := p2_concentrating_delta_lower hn (parisiMix μ ν θ) β lam r q hβ hr hq hlam hfloor hprofile
  have hΔunit := vectorConcentratingDelta_mem_unit (n := n) (parisiMix μ ν θ) β (1-r) (lam/β)
    hβp.ne' (by linarith [hr.1]) (q/4) (q/2) (by linarith [hq.1])
    (by linarith [hq.2]) (half_pos hq.1)
  have hSign := concentrating_physical_signal_lower (n := n) μ ν (parisiMix μ ν θ)
    β (1-r) lam (q/4) (q/2) (k*q/8) (by linarith [hr.1]) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2]) (by simpa only [hE] using hsignal)
  have hSign' : (k*q/8)*Δ ≤ r*S := by
    convert hSign using 1
    dsimp only [S,responseC1Signal,w,concentratingResponseTest]
    congr 1
    ring
  have hSlow : (responseCurvatureConstant 2)^2*k*q^2/30 ≤ S := by
    have hm := mul_le_mul_of_nonneg_left hΔ (show 0 ≤ k*q/8 by positivity [hq.1])
    change (k*q/8)*(r*(responseCurvatureConstant 2)^2*(4*q/15)) ≤ (k*q/8)*Δ at hm
    have he : (k*q/8)*(r*(responseCurvatureConstant 2)^2*(4*q/15)) =
        r*((responseCurvatureConstant 2)^2*k*q^2/30) := by ring
    rw [he] at hm
    exact (mul_le_mul_iff_right₀ hr.1).mp (hm.trans hSign')
  have hD := p2_concentrating_denominator_local_bound hn μ ν β (1-r) lam θ (q/4) (q/2)
    (2/(Real.sqrt r*Real.sqrt q)) (Cs+1/(Real.sqrt r*q*Real.sqrt q)) hβp
    (by linarith [hr.1]) (half_pos hq.1) (by linarith [hq.1]) (by linarith [hq.2]) (by positivity [hr.1,hq.1])
    (fun x hx => p2_response_mean_upper hn (parisiMix μ ν θ) β lam r q hβp hr.1 hq
      (by simpa only [hE] using hx)) (by simpa only [hE] using hdensity)
  have hScale := p2_denominator_scaling_bound r q Cs Δ hr hq hCs hΔunit
  refine ⟨by positivity [hr.1,hq.1],hD.trans hScale,?_⟩
  rw [p2_curvature_coefficient_identity r q k Cs hr.1 hq.1 hCs]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity : 0 ≤ (responseCurvatureConstant 2)^2*k*q^2/30) hSlow 2)
    (by positivity [hr.1])

theorem p2_midpoint_response_gain (hn : 0 < n) (μ ν : Paper.ParisiMeasure)
    (β lam r q k Cs : ℝ) (hβ : 1 ≤ β) (hr : r ∈ Ioc (0 : ℝ) 1)
    (hq : q ∈ Ioc (0 : ℝ) (1/4)) (hk : 0 < k) (hCs : 0 ≤ Cs) (hlam : 0 ≤ lam)
    (hfloor : ∀θ ∈ Ioo (0 : ℝ) 1, lam ≤ β*parisiCDF (parisiMix μ ν θ) 0)
    (hprofile : ∀θ ∈ Ioo (0 : ℝ) 1, ∀x ∈ Icc (q/4) (3*q/4), β*parisiCDF (parisiMix μ ν θ) x ≤ 2)
    (hdensity : ∀θ ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal β •
      (parisiCDFPrimitive (parisiMix μ ν θ)).measure.restrict (Ioo (q/4) (3*q/4)) ≤
      ENNReal.ofReal (Cs+1/(Real.sqrt r*q*Real.sqrt q)) • volume.restrict (Ioo (q/4) (3*q/4)))
    (hsignal : ∀x ∈ Ioo (q/4) (3*q/4), k*q/8 ≤ β*(parisiCDF ν x-parisiCDF μ x)) :
    p2MidpointConstant k Cs*r^3*Real.sqrt r*q^5*Real.sqrt q ≤
      responseEnergyFunctional n μ β (1-r) lam+responseEnergyFunctional n ν β (1-r) lam-
        2*responseEnergyFunctional n (parisiMix μ ν (1/2)) β (1-r) lam := by
  let w := concentratingResponseTest (q/4) (q/2) (half_pos hq.1)
    (by linarith [hq.1]) (by linarith [hq.2])
  have hEnvelope := fun θ hθ => p2_concentrating_response_envelope hn μ ν β lam r q k Cs θ
    hβ hr hq hk hCs hlam (hfloor θ hθ) (hprofile θ hθ) (hdensity θ hθ) hsignal
  have hh := response_C1_full_midpoint_lower hn μ ν β (1-r) lam (by linarith) (by linarith [hr.1]) hlam w
    (fun _ => (32+2*Cs)/(Real.sqrt r*q*Real.sqrt q))
    (4*p2MidpointConstant k Cs*r^3*Real.sqrt r*q^5*Real.sqrt q)
    (by unfold p2MidpointConstant;positivity [hr.1,hq.1])
    (fun θ hθ => (hEnvelope θ hθ).1)
    (fun θ hθ => (hEnvelope θ hθ).2.1)
    (fun θ hθ => by
      convert (hEnvelope θ hθ).2.2 using 1 <;> ring)
  convert hh using 1 <;> ring

end QuantitativePaper
