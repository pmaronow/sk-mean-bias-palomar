module
public import HexagonPaper.CavityFixedRowExpansionMarkedFubini

@[expose] public section

/-! Integrable sections of actual all-profile marked bounded families. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
variable {n : ℕ} {I : Type*} [MeasurableSpace I]

theorem integrable_cavityMarkedScalar_family_section
    (μ : Paper.ParisiMeasure) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (ν : Measure I) [IsFiniteMeasure ν] (p r l : I→Paper.Overlap)
    (hp : Measurable p) (hr : Measurable r) (hl : Measurable l)
    (F : I×(AnisotropicDisorderBrownianSample n×Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C) (j : Fin 8) :
    Integrable (fun z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1)=>
      ∫i,F (i,(cavityZeroMarkedSampleSplit n z).1)*
        scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p i) (r i) (l i)
          (cavityZeroMarkedSampleSplit n z).2 ∂ν)
      (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a) :=
  (integrable_cavityMarkedScalar_family μ β ρ hβ hρ a ν p r l hp hr hl F hF C hC hb j).integral_prod_right

end HexagonPaper
