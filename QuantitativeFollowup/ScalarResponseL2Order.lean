module
public import QuantitativeFollowup.ScalarResponseL2Operator
public import QuantitativeFollowup.ScalarResponseDomination
public import FourPapersCommon.BoundedL2Multiplier

@[expose] public section

/-! Literal Hilbert-space multiplier domination of the actual scalar
response, transferred from the proved dense-test quadratic inequality. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace QuantitativeFollowup
open Paper FRSB QuantitativePaper FourPapersCommon
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def scalarGammaMultiplierCoefficient (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) : C(Paper.Overlap,ℝ) :=
  ⟨fun q=>GammaPrime β μ q,by
    have harg : Continuous (fun q : Paper.Overlap=>(μ,q)):=continuous_const.prodMk continuous_id
    convert! (continuous_scalarGammaPrime_parameter β hβ).comp harg using 1⟩

theorem scalarGammaMultiplierCoefficient_norm_le (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure)
    (q : Paper.Overlap) : ‖scalarGammaMultiplierCoefficient β hβ μ q‖ ≤ β^2 := by
  change ‖GammaPrime β μ q‖ ≤ β^2
  rw [Real.norm_of_nonneg (GammaPrime_pos β hβ μ q.property).le]
  exact GammaPrime_le_beta_sq β hβ μ q.property

def scalarGammaL2Multiplier (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ) :
    endpointFixedL2 (parisiFreeMeasure μ a)→L[ℝ]endpointFixedL2 (parisiFreeMeasure μ a) :=
  endpointFixedL2Multiplier (parisiFreeMeasure μ a) (scalarGammaMultiplierCoefficient β hβ μ)
    (scalarGammaMultiplierCoefficient β hβ μ).continuous.measurable (β^2)
    (scalarGammaMultiplierCoefficient_norm_le β hβ μ)

theorem scalarGammaL2Multiplier_inner (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (f : endpointFixedL2 (parisiFreeMeasure μ a)) :
    inner ℝ f (scalarGammaL2Multiplier β hβ μ a f)=∫q : Paper.Overlap,GammaPrime β μ q*(f.val q)^2 ∂parisiFreeMeasure μ a :=
  endpointFixedL2Multiplier_inner _ _ _ _ _ f

theorem scalarGammaL2Multiplier_test_pairing (β : ℝ) (hβ : β≠0) (μ : Paper.ParisiMeasure) (a : ℝ)
    (φ : endpointFixedLipschitzTests) :
    inner ℝ (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ)
      (scalarGammaL2Multiplier β hβ μ a (endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a) φ))=
      ∫q : Paper.Overlap,GammaPrime β μ q*φ.val q^2 ∂parisiFreeMeasure μ a := by
  rw [scalarGammaL2Multiplier_inner]
  apply integral_congr_ae
  filter_upwards [φ.val.coeFn_toLp (p:=2) (μ:=parisiFreeMeasure μ a) (𝕜:=ℝ)] with q hq
  change GammaPrime β μ q*((ContinuousMap.toLp 2 (parisiFreeMeasure μ a) ℝ φ.val) q)^2=_
  rw [hq]

theorem scalarResponseL2Operator_le_multiplier (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (f : endpointFixedL2 (parisiFreeMeasure μ a)) :
    inner ℝ f (scalarResponseL2Operator β hβ.ne' μ a ha hμ f) ≤ inner ℝ f (scalarGammaL2Multiplier β hβ.ne' μ a f) := by
  let e := endpointFixedLipschitzLinearEmbedding (parisiFreeMeasure μ a)
  let J := scalarResponseL2Operator β hβ.ne' μ a ha hμ
  let K := scalarGammaL2Multiplier β hβ.ne' μ a
  have hd : DenseRange e := endpointFixedLipschitzLinearEmbedding_denseRange _
  refine hd.induction_on (p:=fun f=>inner ℝ f (J f) ≤ inner ℝ f (K f)) f ?_ ?_
  · exact isClosed_le (continuous_id.inner J.continuous) (continuous_id.inner K.continuous)
  intro φ
  change inner ℝ (e φ) (scalarResponseL2Operator β hβ.ne' μ a ha hμ (e φ)) ≤ inner ℝ (e φ) (scalarGammaL2Multiplier β hβ.ne' μ a (e φ))
  rw [scalarResponseL2Operator_test_pairing,scalarGammaL2Multiplier_test_pairing]
  obtain ⟨L,hφ⟩:=φ.property.2.2
  exact scalar_response_multiplier_domination β hβ μ a ha hμ φ.val L hφ φ.property.1 φ.property.2.1

theorem scalarResponseL2Operator_quadratic_domination (β : ℝ) (hβ : 0<β) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a∈Icc (0:ℝ) 1) (hμ : μ∈scalarFloor a)
    (f : endpointFixedL2 (parisiFreeMeasure μ a)) :
    inner ℝ f (scalarResponseL2Operator β hβ.ne' μ a ha hμ f) ≤
      ∫q : Paper.Overlap,GammaPrime β μ q*(f.val q)^2 ∂parisiFreeMeasure μ a := by
  simpa only [scalarGammaL2Multiplier_inner] using scalarResponseL2Operator_le_multiplier β hβ μ a ha hμ f

end QuantitativeFollowup
