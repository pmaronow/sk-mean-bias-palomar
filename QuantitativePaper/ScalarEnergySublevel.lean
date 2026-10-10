module
public import QuantitativePaper.ZeroTemperatureControlFunctional
public import Paper.ParisiCDFIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

/-! A scalar energy sublevel bounds the actual rescaled CDF on the early
half interval by a constant independent of inverse temperature. -/
noncomputable section
open Set MeasureTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 800000

theorem half_weighted_profile_mass_le_zeroTemperatureFunctional
    (γ : ℝ→ℝ) (hγ : Measurable γ)
    (hiγ : IntervalIntegrable γ volume (0:ℝ) 1) :
    (1/2:ℝ)*(∫q in (0:ℝ)..1,(1-q)*γ q)≤zeroTemperatureFunctional γ := by
  have hj:=intervalIntegrable_zeroTemperatureCorrection γ hγ hiγ
  have he : (∫q in (0:ℝ)..1,(1-q)*γ q)=
      (∫q in (0:ℝ)..1,γ q)-(∫q in (0:ℝ)..1,q*γ q) := by
    simp_rw [show ∀q:ℝ,(1-q)*γ q=γ q-q*γ q by intro q;ring]
    exact intervalIntegral.integral_sub hiγ hj
  rw [he]
  have hv:=zeroTemperatureValue_ge_half_mass γ hγ hiγ
  unfold zeroTemperatureFunctional
  linarith

theorem half_weighted_cdf_mass_le_scalarEnergyFunctional
    (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure) :
    (1/2:ℝ)*(∫q in (0:ℝ)..1,(1-q)*(β*parisiCDF μ q))≤
      scalarParisiFunctional β μ/β :=
  (half_weighted_profile_mass_le_zeroTemperatureFunctional _
    ((parisiCDF_measurable μ).const_mul β)
    ((parisiCDF_intervalIntegrable μ 0 1).const_mul β)).trans
      (zeroTemperatureFunctional_parisi_sandwich β hβ μ).1

theorem scalarEnergyFunctional_ge_early_cdf (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) :
    β*parisiCDF μ (1/2)/16 ≤ scalarParisiFunctional β μ/β := by
  let γ : ℝ→ℝ:=fun q=>β*parisiCDF μ q
  have hm : Measurable γ:=(parisiCDF_measurable μ).const_mul β
  have hi (a b : ℝ) : IntervalIntegrable γ volume a b:=
    (parisiCDF_intervalIntegrable μ a b).const_mul β
  have hj (a b : ℝ) : IntervalIntegrable (fun q=>(1-q)*γ q) volume a b := by
    have hc : Continuous (fun q:ℝ=>1-q):=by fun_prop
    simpa only [mul_comm] using (hi a b).mul_continuousOn hc.continuousOn
  have hzero : 0≤∫q in (0:ℝ)..(1/2:ℝ),(1-q)*γ q := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro q hq
    exact mul_nonneg (by linarith [hq.2])
      (mul_nonneg hβ.le (parisiCDF_nonneg μ q))
  have hhalf : γ (1/2)/8≤∫q in (1/2:ℝ)..1,(1-q)*γ q := by
    have hmono : (∫q in (1/2:ℝ)..1,(1-q)*γ (1/2))≤
        ∫q in (1/2:ℝ)..1,(1-q)*γ q := by
      have hc : Continuous (fun q:ℝ=>(1-q)*γ (1/2)):=by fun_prop
      apply intervalIntegral.integral_mono_on (by norm_num)
        (hc.intervalIntegrable (1/2) 1)
        (hj (1/2) 1)
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (by linarith [hq.2])
      exact mul_le_mul_of_nonneg_left (parisiCDF_monotone μ hq.1) hβ.le
    have he : (∫q in (1/2:ℝ)..1,(1-q)*γ (1/2))=γ (1/2)/8 := by
      rw [intervalIntegral.integral_mul_const]
      have hs : (∫q in (1/2:ℝ)..1,1-q)=
          (∫q in (1/2:ℝ)..1,(1:ℝ))-(∫q in (1/2:ℝ)..1,q) := by
        simpa only [Pi.sub_apply] using intervalIntegral.integral_sub
          (f:=fun _:ℝ=>1) (g:=fun q:ℝ=>q) intervalIntegrable_const
          (continuous_id.intervalIntegrable (1/2:ℝ) 1)
      rw [hs,intervalIntegral.integral_const,integral_id]
      norm_num
      <;> ring
    rwa [he] at hmono
  have hadd:=intervalIntegral.integral_add_adjacent_intervals (hj 0 (1/2)) (hj (1/2) 1)
  have hbound:=half_weighted_cdf_mass_le_scalarEnergyFunctional β hβ μ
  change (1/2:ℝ)*(∫q in (0:ℝ)..1,(1-q)*γ q)≤_ at hbound
  change γ (1/2)/16≤_
  linarith

theorem scalarEnergy_sublevel_cdf_le (β B : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hcost : scalarParisiFunctional β μ/β ≤ B)
    (q : ℝ) (hq : q≤1/2) : β*parisiCDF μ q≤16*B := by
  have hb:=scalarEnergyFunctional_ge_early_cdf β hβ μ
  have hmono:=mul_le_mul_of_nonneg_left (parisiCDF_monotone μ hq) hβ.le
  linarith

theorem scalarEnergy_sublevel_two_cdf_le (β : ℝ) (hβ : 0<β)
    (μ : Paper.ParisiMeasure) (hcost : scalarParisiFunctional β μ/β ≤ 2)
    (q : ℝ) (hq : q≤1/2) : β*parisiCDF μ q≤32 := by
  simpa only [show (16:ℝ)*2=32 by norm_num] using
    scalarEnergy_sublevel_cdf_le β 2 hβ μ hcost q hq

end QuantitativePaper
