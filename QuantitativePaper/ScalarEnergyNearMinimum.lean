module
public import QuantitativePaper.ScalarEnergySublevel
public import QuantitativePaper.ScalarEnergyCrudeUpper

@[expose] public section

/-! Actual near-minimum scalar profiles and all their mixtures have the
temperature-independent early CDF bound required by the root argument. -/
noncomputable section
open Set Paper
namespace QuantitativePaper

theorem scalarEnergy_near_minimum_cost_lt_two (β : ℝ) (hβ : 1≤β)
    (μ : Paper.ParisiMeasure)
    (hcost : scalarParisiFunctional β μ/β ≤ scalarEnergyValue β 0+1/2) :
    scalarParisiFunctional β μ/β<2 := by
  linarith [scalarEnergyValue_zero_lt_three_halves β hβ]

theorem scalarEnergy_near_minimum_cdf_le (β : ℝ) (hβ : 1≤β)
    (μ : Paper.ParisiMeasure)
    (hcost : scalarParisiFunctional β μ/β ≤ scalarEnergyValue β 0+1/2)
    (q : ℝ) (hq : q≤1/2) : β*parisiCDF μ q≤32 :=
  scalarEnergy_sublevel_two_cdf_le β (lt_of_lt_of_le zero_lt_one hβ) μ
    (scalarEnergy_near_minimum_cost_lt_two β hβ μ hcost).le q hq

theorem scalarEnergy_near_minimum_mix_cdf_le (β : ℝ) (hβ : 1≤β)
    (μ ν : Paper.ParisiMeasure)
    (hμ : scalarParisiFunctional β μ/β ≤ scalarEnergyValue β 0+1/2)
    (hν : scalarParisiFunctional β ν/β ≤ scalarEnergyValue β 0+1/2)
    (θ : ℝ) (hθ : θ∈Icc (0:ℝ) 1) (q : ℝ) (hq : q≤1/2) :
    β*parisiCDF (parisiMix μ ν θ) q≤32 := by
  rw [parisiCDF_mix μ ν θ q hθ]
  have hm:=scalarEnergy_near_minimum_cdf_le β hβ μ hμ q hq
  have hn:=scalarEnergy_near_minimum_cdf_le β hβ ν hν q hq
  nlinarith [mul_nonneg (sub_nonneg.mpr hθ.2) (sub_nonneg.mpr hm),
    mul_nonneg hθ.1 (sub_nonneg.mpr hn)]

end QuantitativePaper
