module
public import HexagonPaper.CavityFixedRowExpansionScalarSamples
public import QuantitativeFollowup.FollowupCavityCppZeroResponseNativeProductMoments

@[expose] public section

/-! All-profile contraction of genuinely measurable bounded rest families
with the actual marked scalar samples. Both the complete marked product law
and Fubini integrability are proved inputs from the native factories. -/
noncomputable section
open Set MeasureTheory FourPapersCommon QuantitativePaper QuantitativeFollowup
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ} {I : Type*} [MeasurableSpace I]

theorem integrable_cavityMarkedScalar_family
    (μ : Paper.ParisiMeasure) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (ν : Measure I) [IsFiniteMeasure ν] (p r l : I→Paper.Overlap)
    (hp : Measurable p) (hr : Measurable r) (hl : Measurable l)
    (F : I×(AnisotropicDisorderBrownianSample n×Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C) (j : Fin 8) :
    Integrable (fun z : I×(AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))=>
      F (z.1,(cavityZeroMarkedSampleSplit n z.2).1)*
        scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p z.1) (r z.1) (l z.1)
          (cavityZeroMarkedSampleSplit n z.2).2)
      (ν.prod (anisotropicMeasureSpinPathLaw
        (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)) := by
  have hs : Measurable (fun z : I×(AnisotropicDisorderBrownianSample (n+1)×Configuration (n+1))=>
      cavityZeroMarkedSampleSplit n z.2):=
    (measurable_cavityZeroMarkedSampleSplit n).comp measurable_snd
  have hmF := hF.comp (measurable_fst.prodMk hs.fst)
  have hmG := (measurable_cavityScalarResponseSample_levels j (followupCavityScalarBeta n β ρ)
    (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ).comp
      (((hp.comp measurable_fst).prodMk ((hr.comp measurable_fst).prodMk
        (hl.comp measurable_fst))).prodMk hs.snd)
  exact (integrable_const (C*(1+2*Real.exp ((followupCavityScalarBeta n β ρ)^2)))).mono'
    (hmF.mul hmG).aestronglyMeasurable (.of_forall fun z=>by
      rw [norm_mul]
      exact mul_le_mul (hb _) (norm_scalarResponseSample_le j _ μ _ _ _ _)
        (norm_nonneg _) hC)

theorem cavityMarkedScalar_family_integral
    (μ : Paper.ParisiMeasure) (β ρ : ℝ) (hβ : 0<β) (hρ : ρ∈Ioc (0:ℝ) 1) (a : ℝ)
    (ν : Measure I) [IsFiniteMeasure ν] (p r l : I→Paper.Overlap)
    (hp : Measurable p) (hr : Measurable r) (hl : Measurable l)
    (F : I×(AnisotropicDisorderBrownianSample n×Configuration n)→ℝ) (hF : Measurable F)
    (C : ℝ) (hC : 0≤C) (hb : ∀z,‖F z‖≤C) (j : Fin 8) :
    (∫z,∫i,F (i,(cavityZeroMarkedSampleSplit n z).1)*
      scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p i) (r i) (l i)
        (cavityZeroMarkedSampleSplit n z).2 ∂ν
      ∂anisotropicMeasureSpinPathLaw (followupCavitySpinModel n β ρ hβ hρ 0 ⟨le_rfl,zero_le_one⟩) μ a)=
      ∫i,(∫z,F (i,z) ∂anisotropicMeasureSpinPathLaw (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*
        scalarResponseCoefficient j (followupCavityScalarBeta n β ρ) μ (p i) (r i) (l i) ∂ν := by
  have hi:=integrable_cavityMarkedScalar_family μ β ρ hβ hρ a ν p r l hp hr hl F hF C hC hb j
  rw [←integral_integral_swap hi]
  apply integral_congr_ae
  exact .of_forall fun i=>by
    dsimp only
    exact (integral_cavityZeroMarked_product μ n β ρ hβ hρ a
      (fun z=>F (i,z)) (scalarResponseSample j (followupCavityScalarBeta n β ρ) μ (p i) (r i) (l i))
      (hF.comp measurable_prodMk_left)
      (measurable_scalarResponseSample j _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ _ _ _)).trans
      (congrArg (fun x=>(∫z,F (i,z) ∂anisotropicMeasureSpinPathLaw
        (followupCavityRestSpinModel n β ρ hβ hρ) μ a)*x)
        (integral_scalarResponseSample j _ (followupCavityScalarBeta_pos n β ρ hβ hρ).ne' μ _ _ _))

end HexagonPaper
