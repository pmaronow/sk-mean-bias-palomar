module
public import QuantitativePaper.ResponseModel
public import QuantitativePaper.VectorFunctionalConvexity
public import QuantitativePaper.ScalarFloorContinuity

@[expose] public section

/-! Literal energy-normalized response functional and admissible profiles.
This closes the convexity clause of Proposition A.2; its quantitative
midpoint improvement remains a separate second-variation obligation. -/
noncomputable section
open Set MeasureTheory
namespace QuantitativePaper
set_option maxHeartbeats 800000

def responseEnergyFunctional (n:ℕ) (μ:Paper.ParisiMeasure) (β t lam:ℝ):ℝ:=
  vectorMeasureFunctional n μ β t (lam/β)/β

def responseProfile (μ:Paper.ParisiMeasure) (β:ℝ) (q:ℝ):ℝ:=β*Paper.parisiCDF μ q

theorem responseEnergyFunctional_mix_convex (n:ℕ) (μ ν:Paper.ParisiMeasure)
    (β t lam:ℝ) (hβ:0<β) (ht:t≤1) (hlam:0≤lam):
    ConvexOn ℝ (Icc (0:ℝ) 1)
      (fun theta=>responseEnergyFunctional n (Paper.parisiMix μ ν theta) β t lam) := by
  have hc:=convexOn_vectorMeasureFunctional_mix n μ ν β t ht (lam/β)
    (div_nonneg hlam hβ.le)
  simpa only [responseEnergyFunctional,div_eq_mul_inv,mul_comm,smul_eq_mul] using
    hc.smul (show 0≤β⁻¹ from inv_nonneg.mpr hβ.le)

theorem responseProfile_mix (μ ν:Paper.ParisiMeasure) (β theta q:ℝ)
    (htheta:theta∈Icc (0:ℝ) 1):
    responseProfile (Paper.parisiMix μ ν theta) β q=
      (1-theta)*responseProfile μ β q+theta*responseProfile ν β q := by
  unfold responseProfile
  rw [Paper.parisiCDF_mix μ ν theta q htheta]
  ring

theorem responseProfile_admissible_lower {μ:Paper.ParisiMeasure} {β lam:ℝ}
    (hβ:0<β) (hμ:μ∈scalarFloor (lam/β)) {q:ℝ} (hq:0≤q):
    lam≤responseProfile μ β q := by
  have hh:=mul_le_mul_of_nonneg_left (scalarFloor_cdf_lower hμ hq) hβ.le
  rw [mul_div_cancel₀ _ hβ.ne'] at hh
  exact hh

end QuantitativePaper
