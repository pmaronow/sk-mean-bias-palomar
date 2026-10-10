module
public import QuantitativePaper.ResponseBounds

@[expose] public section

/-! Atom-retaining Stieltjes budget for the scalar Fisher midpoint argument.
The upper bound uses the mass of the actual closed overlap band. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace QuantitativePaper
variable {n : ℕ}
set_option maxHeartbeats 1000000

theorem response_curvature_band_budget (μ : Paper.ParisiMeasure) (β t lam l u C U : ℝ)
    (hβ : 0≤β) (ht : t<1) (hC : 0≤C)
    (hζ : ∀q : Paper.Overlap,(q:ℝ)∈Icc l u→
      responseAveragedCurvature (n:=n) μ β t lam ht.le q≤C)
    (hCDF : β*Paper.parisiCDF μ u≤U) :
    β*(∫q : Paper.Overlap in {q : Paper.Overlap | (q:ℝ)∈Icc l u},
      responseAveragedCurvature (n:=n) μ β t lam ht.le q ∂(μ : Measure Paper.Overlap))≤C*U := by
  let A : Set Paper.Overlap := {q | (q:ℝ)∈Icc l u}
  have hA : MeasurableSet A := measurableSet_Icc.preimage measurable_subtype_coe
  have hζLp : MemLp (responseAveragedCurvature (n:=n) μ β t lam ht.le) 2
      (μ : Measure Paper.Overlap) := by
    apply MemLp.of_bound (continuous_responseAveragedCurvature μ β t lam ht).measurable.aestronglyMeasurable
      (|β^2/(n:ℝ)| * (n:ℝ)^3)
    exact Filter.Eventually.of_forall fun q => norm_responseAveragedCurvature_le μ β t lam ht.le q
  have hi := hζLp.integrable one_le_two
  have hh := setIntegral_mono_on (hi.restrict (s:=A))
    (integrable_const C : Integrable (fun _ : Paper.Overlap => C)
      ((μ : Measure Paper.Overlap).restrict A)) hA (fun q hq => hζ q hq)
  simp only [integral_const,smul_eq_mul,measureReal_restrict_apply_univ] at hh
  have hmass : (μ : Measure Paper.Overlap).real A≤Paper.parisiCDF μ u := by
    exact measureReal_mono (fun q hq => hq.2)
  have hprod := mul_le_mul_of_nonneg_left hh hβ
  have hCDF' := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hmass hβ) hC
  have hlast := mul_le_mul_of_nonneg_left hCDF hC
  change β*(∫q in A,responseAveragedCurvature (n:=n) μ β t lam ht.le q
    ∂(μ : Measure Paper.Overlap))≤C*U
  nlinarith

end QuantitativePaper
