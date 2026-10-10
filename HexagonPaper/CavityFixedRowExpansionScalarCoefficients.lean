module
public import HexagonPaper.CavityFixedRowExpansionScalarSamples

@[expose] public section

/-! Actual marked scalar expectation coefficients are jointly continuous
and uniformly bounded at all levels, for every probability profile. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
open scoped Topology
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem continuous_cavityScalarResponseCoefficient_levels (j : Fin 8) (B : ℝ) (hB : B≠0)
    (μ : Paper.ParisiMeasure) :
    Continuous (fun x : CavityScalarSampleLevels=>scalarResponseCoefficient j B μ x.1 x.2.1 x.2.2) := by
  have he : (fun x : CavityScalarSampleLevels=>scalarResponseCoefficient j B μ x.1 x.2.1 x.2.2)=
      fun x=>∫z,scalarResponseSample j B μ x.1 x.2.1 x.2.2 z ∂scalarMarkedSpinLaw B hB μ := by
    funext x
    exact (integral_scalarResponseSample j B hB μ x.1 x.2.1 x.2.2).symm
  rw [he]
  apply continuous_of_dominated (bound:=fun _=>1+2*Real.exp (B^2))
  · intro x
    exact (measurable_scalarResponseSample j B hB μ x.1 x.2.1 x.2.2).aestronglyMeasurable
  · intro x
    exact .of_forall fun z=>norm_scalarResponseSample_le j B μ x.1 x.2.1 x.2.2 z
  · exact integrable_const _
  · exact .of_forall fun z=>continuous_cavityScalarResponseSample_levels j B hB μ z

theorem norm_cavityScalarResponseCoefficient_le (j : Fin 8) (B : ℝ) (hB : B≠0)
    (μ : Paper.ParisiMeasure) (p r l : Paper.Overlap) :
    ‖scalarResponseCoefficient j B μ p r l‖≤1+2*Real.exp (B^2) := by
  rw [←integral_scalarResponseSample j B hB μ p r l]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=scalarMarkedSpinLaw B hB μ) (.of_forall fun z=>norm_scalarResponseSample_le j B μ p r l z)

end HexagonPaper
