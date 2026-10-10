module
public import QuantitativePaper.UniformScalarTrialBackward

@[expose] public section

/-! Literal actual clipped scalar energy cost, with a coefficient that
contains no inverse-temperature dependence. -/
noncomputable section
open Set MeasureTheory Filter Paper FRSB FourPapersCommon QuantitativeFollowup
open scoped Topology NNReal
namespace QuantitativePaper
set_option maxHeartbeats 2200000

def scalarUniformClippingConstant (C L : ℝ) : ℝ :=
  C^2*Real.exp (9*L^2+2*L*C+1)*(1+L)+1

theorem scalarClipped_functional_uniform_energy_cost_le
    (s : ℝ) (hs : s∈Icc (0:ℝ) 1) (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q∈Ioo (0:ℝ) 1) (hsupp : parisiSupport μ=Icc (0:ℝ) q)
    (lam C L T : ℝ) (hlam : β*s=lam) (hlamL : lam≤L) (hC : 0≤C) (hL : 0≤L)
    (hT : 0<T) (hTq : T<q) (hfloor : s≤parisiCDF μ T)
    (hcoeff : ∀t∈Icc (0:ℝ) T,β*parisiCDF μ t≤L)
    (hH : ∀t∈Icc (0:ℝ) T,∀x,β*parisiHessian β μ (t,x)≤C) :
    (parisiPDEFunctional β 0 (scalarClippedTrialMeasure s hs μ)-parisiPDEFunctional β 0 μ)/β≤
      scalarUniformClippingConstant C L*lam^2*T^3 := by
  let ν:=scalarClippedTrialMeasure s hs μ
  let Y:=scalarSquareDifferenceMomentReal β hβ.ne' μ ν
  let mR : ℝ→ℝ:=fun t=>∫ω,scalarClippingCostSource β μ ν
    (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)/β∂canonicalBrownianMeasure
  have hmI : IntervalIntegrable mR volume 0 T := by
    have hh:=intervalIntegrable_bounded_source_expectation (P:=canonicalBrownianMeasure)
      (fun t ω=>scalarClippingCostSource β μ ν
        (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω))
      ((measurable_scalarClippingCostSource β μ ν).comp
        (measurable_fst.prodMk (measurable_selectedState_real β hβ.ne' μ)))
      (4*β^2) (fun t ω=>norm_scalarClippingCostSource_le β μ ν _) 0 T
    simpa only [mR,integral_div] using hh.div_const β
  have hYc : Continuous Y := continuous_scalarSquareDifferenceMomentReal β hβ.ne' μ ν
  have hmono:=intervalIntegral.integral_mono_on hT.le hmI
    ((((hYc.intervalIntegrable 0 T).const_mul (1/T+L)).add
      ((continuous_id.intervalIntegrable 0 T).const_mul (lam^2*T))).const_mul (1/2:ℝ))
    (fun t ht=>scalarClipped_cost_source_expectation_uniform_le s hs β hβ μ hmin q hq hsupp
      lam L T t hlam hlamL hT ⟨ht.1,ht.2.trans hTq.le⟩ (hcoeff t ht))
  change (∫t in 0..T,mR t)≤∫t in 0..T,(1/2:ℝ)*((1/T+L)*Y t+lam^2*T*t) at hmono
  have hidi : IntervalIntegrable (fun t:ℝ=>t) volume 0 T := continuous_id.intervalIntegrable 0 T
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((hYc.intervalIntegrable 0 T).const_mul _) (hidi.const_mul _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul] at hmono
  have hYI : (∫t in 0..T,Y t)≤lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^4 := by
    have hh:=intervalIntegral.integral_mono_on hT.le (hYc.intervalIntegrable 0 T)
      (intervalIntegrable_const (μ:=volume) (c:=lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^3))
      (scalarClipped_square_uniform_energy_bound s hs β hβ μ hmin q hq hsupp
        lam C L T hlam hlamL hC hL hT hTq hfloor hcoeff hH)
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,pow_succ,
      mul_assoc,mul_left_comm,mul_comm] using hh
  have hiT : (∫t in (0:ℝ)..T,t)≤T^2 := by
    have hh:=intervalIntegral.integral_mono_on hT.le hidi
      (intervalIntegrable_const (μ:=volume) (c:=T)) (fun t ht=>ht.2)
    simpa only [intervalIntegral.integral_const,sub_zero,smul_eq_mul,pow_two] using hh
  have hYmul:=mul_le_mul_of_nonneg_left hYI (show 0≤(1/2:ℝ)*(1/T+L) by positivity)
  have htMul:=mul_le_mul_of_nonneg_left hiT (show 0≤(1/2:ℝ)*(lam^2*T) by positivity)
  have ht1 : T≤1 := hTq.le.trans hq.2.le
  have he : (1/T+L)*T^4=T^3*(1+L*T) := by field_simp <;> ring
  have hTpow : (1/2:ℝ)*(1/T+L)*(lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^4)≤
      (1/2:ℝ)*lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^3*(1+L) := by
    calc
      _=(1/2:ℝ)*lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*(T^3*(1+L*T)) := by rw [←he];ring
      _≤(1/2:ℝ)*lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*(T^3*(1+L)) := by
        gcongr
        exact (mul_le_mul_of_nonneg_left ht1 hL).trans_eq (mul_one _)
      _=_ := by ring
  rw [scalarClipped_functional_cost_integral s hs β hβ.ne' μ hmin q hq hsupp T hT.le hTq hfloor,
    ←intervalIntegral.integral_div]
  have heq : (fun t:ℝ=>(∫ω,scalarClippingCostSource β μ ν
    (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)∂canonicalBrownianMeasure)/β)=mR := by
    funext t
    rw [←integral_div]
  change (∫t in 0..T,(∫ω,scalarClippingCostSource β μ ν
    (t,selectedParisiItoState β 0 hβ.ne' μ t.toNNReal ω)∂canonicalBrownianMeasure)/β)≤_
  rw [heq]
  have hp : 0≤lam^2*T^3 := by positivity
  have hpc : 0≤C^2*Real.exp (9*L^2+2*L*C+1)*(1+L) := by positivity
  unfold scalarUniformClippingConstant
  calc
    _≤(1/2:ℝ)*((1/T+L)*(∫t in 0..T,Y t)+lam^2*T*(∫t in (0:ℝ)..T,t)) := hmono
    _=(1/2:ℝ)*(1/T+L)*(∫t in 0..T,Y t)+(1/2:ℝ)*(lam^2*T)*(∫t in (0:ℝ)..T,t) := by ring
    _≤(1/2:ℝ)*lam^2*C^2*Real.exp (9*L^2+2*L*C+1)*T^3*(1+L)+(1/2:ℝ)*(lam^2*T)*T^2 :=
      add_le_add (hYmul.trans hTpow) htMul
    _≤_ := by nlinarith only [hp,mul_nonneg hp hpc]

end QuantitativePaper
