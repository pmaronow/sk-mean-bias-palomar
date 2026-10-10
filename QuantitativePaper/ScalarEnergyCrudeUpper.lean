module
public import QuantitativePaper.ScalarEnergyFunctionalIdentification
public import QuantitativePaper.ZeroTemperatureControlFunctional
public import FourPapersCommon.GaussianAbsoluteMoment
public import Paper.RSFunctional
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-! A temperature-independent scalar comparison obtained from the genuine
Dirac-at-one trial and the exact first absolute Gaussian moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace QuantitativePaper
set_option maxHeartbeats 800000

theorem zeroTemperatureFunctional_zero :
    zeroTemperatureFunctional (fun _=>0)=Real.sqrt (2/Real.pi) := by
  have ho (A : ℝ→BrownianSample→ℝ) :
      zeroControlObjective (fun _=>0) 0 A=
        ∫ω,|canonicalBrownian 1 ω| ∂canonicalBrownianMeasure := by
    simp [zeroControlObjective,zeroControlPayoff,zeroControlEndpoint,zeroControlCost]
  have he : zeroControlValues (fun _=>0) 0=
      {∫ω,|canonicalBrownian 1 ω| ∂canonicalBrownianMeasure} := by
    ext v
    constructor
    · rintro ⟨A,hA,rfl⟩
      exact ho A
    · intro hv
      refine ⟨fun _ _=>0,admissible_zeroControl,?_⟩
      exact hv.trans (ho _).symm
  unfold zeroTemperatureFunctional zeroTemperatureValue
  rw [he,csSup_singleton]
  simp only [mul_zero,intervalIntegral.integral_zero,sub_zero]
  have h:= (FRSB.hasLaw_scaledBrownian (1:ℝ) 1).integral_comp
    (f:=fun x:ℝ=>|x|) (by fun_prop)
  simpa only [one_mul,one_pow,NNReal.coe_one,Real.toNNReal_one,
    Function.comp_apply,FourPapersCommon.integral_abs_standardGaussian] using h

theorem scalarEnergyValue_zero_le_gaussian_trial (β : ℝ) (hβ : 0<β) :
    scalarEnergyValue β 0 ≤ Real.sqrt (2/Real.pi)+Real.log 2/β := by
  let μ : Paper.ParisiMeasure:=diracOverlap 1 (by norm_num)
  have hc:=constrainedParisiValue_le β 0 (by norm_num) μ (by simp)
  have hh:=(zeroTemperatureFunctional_parisi_sandwich β hβ μ).2
  have hz : zeroTemperatureFunctional (fun q=>β*parisiCDF μ q)=
      zeroTemperatureFunctional (fun _=>0) := by
    apply zeroTemperatureFunctional_congr_Ioo
    intro q hq
    simp [μ,parisiCDF_dirac,not_le.mpr hq.2]
  rw [hz,zeroTemperatureFunctional_zero] at hh
  change constrainedParisiValue β (0/β)/β ≤ _
  rw [zero_div]
  exact (div_le_div_of_nonneg_right hc hβ.le).trans hh

theorem sqrt_two_div_pi_lt_four_fifths :
    Real.sqrt (2/Real.pi)<4/5 := by
  have hpi : (25/8:ℝ)<Real.pi:=by linarith [Real.pi_gt_d2]
  have hs:=Real.sq_sqrt (show 0≤2/Real.pi by positivity)
  have hd : 2/Real.pi<(4/5:ℝ)^2:=by
    apply (div_lt_iff₀ Real.pi_pos).mpr
    nlinarith
  have hn:=Real.sqrt_nonneg (2/Real.pi)
  nlinarith

theorem scalarEnergyValue_zero_lt_three_halves (β : ℝ) (hβ : 1≤β) :
    scalarEnergyValue β 0<3/2 := by
  have hb : 0<β:=lt_of_lt_of_le zero_lt_one hβ
  have hh:=scalarEnergyValue_zero_le_gaussian_trial β hb
  have hl : Real.log 2/β≤Real.log 2:=by
    apply (div_le_iff₀ hb).mpr
    have hp : 0≤Real.log 2:=Real.log_nonneg (by norm_num)
    nlinarith
  have hlog : Real.log 2<(7/10:ℝ):=by linarith [Real.log_two_lt_d9]
  linarith [sqrt_two_div_pi_lt_four_fifths]

theorem scalarEnergy_minimizer_cost_lt_three_halves (β : ℝ) (hβ : 1≤β)
    (μ : Paper.ParisiMeasure) (hμ : FRSB.IsParisiMinimizer β 0 μ) :
    scalarParisiFunctional β μ/β<3/2 := by
  rw [←scalarEnergyValue_zero_of_minimizer β μ hμ]
  exact scalarEnergyValue_zero_lt_three_halves β hβ

end QuantitativePaper
