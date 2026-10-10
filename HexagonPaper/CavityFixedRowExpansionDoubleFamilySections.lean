module
public import HexagonPaper.CavityFixedRowExpansionFamilySections

@[expose] public section

/-! Honest double free-level Fubini for native marked bounded families. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {I : Type*} [MeasurableSpace I]

theorem cavityMarkedScalar_double_family_data
    (μ : Paper.ParisiMeasure) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (ν : Measure I) [IsFiniteMeasure ν] (p r l : I×I→Paper.Overlap)
    (hp : Measurable p) (hr : Measurable r) (hl : Measurable l)
    (F : (I×I)×(AnisotropicDisorderBrownianSample n×Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C) (j : Fin 8) :
    let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
    let G:=fun (x y : I) (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))=>
      F ((x,y),(cavityZeroMarkedSampleSplit n z).1)*
        scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p (x,y)) (r (x,y)) (l (x,y))
          (cavityZeroMarkedSampleSplit n z).2
    Integrable (fun z=>∫x,∫y,G x y z ∂ν ∂ν) P ∧
      (∫z,∫x,∫y,G x y z ∂ν ∂ν ∂P)=∫x,∫y,∫z,G x y z ∂P ∂ν ∂ν := by
  dsimp only
  let P:=anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a
  let G:=fun (x y : I) (z : AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))=>
      F ((x,y),(cavityZeroMarkedSampleSplit n z).1)*
        scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p (x,y)) (r (x,y)) (l (x,y))
          (cavityZeroMarkedSampleSplit n z).2
  have hi : Integrable (fun z : (I×I)×(AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))=>
      G z.1.1 z.1.2 z.2) ((ν.prod ν).prod P) :=
    integrable_cavityMarkedScalar_family μ β ρ hβ hρ a (ν.prod ν) p r l hp hr hl F hF C hC hb j
  have he : (fun z=>∫x : I×I,G x.1 x.2 z ∂ν.prod ν)=ᵐ[P] fun z=>∫x,∫y,G x y z ∂ν ∂ν := by
    filter_upwards [hi.prod_left_ae] with z hz
    exact integral_prod _ hz
  refine ⟨hi.integral_prod_right.congr he,?_⟩
  rw [←integral_congr_ae he,←integral_integral_swap hi]
  exact integral_prod _ hi.integral_prod_left

end HexagonPaper
