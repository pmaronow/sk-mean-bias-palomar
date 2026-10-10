module
public import HexagonPaper.PathHeatContinuousSignedSource

@[expose] public section

/-! Genuine weighted integrability of every term in the printed centered
signed response. Source total variations and explicit derivative bounds,
with the actual common integrable weight envelope, discharge all terms. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BoundedContinuousFunction NNReal
namespace HexagonPaper
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {X Θ Ω : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Θ] [MeasurableSpace Θ] [BorelSpace Θ] [MeasurableSpace Ω]

namespace PathHeatContinuousSignedSource
variable (d : PathHeatContinuousSignedSource Θ X)

def densityContraction (K : X×X→ᵇℝ) (u : Θ) : ℝ :=
  signedContraction K (pathHeatDensityDerivativeMeasure (d.S u) (d.M u))

def centeredContraction (K : X×X→ᵇℝ) (center : ℝ) (u : Θ) : ℝ :=
  signedContraction K
    (pathHeatCenteredDerivativeMeasure (d.S u) (d.P u) (d.M u) (d.Q u) (d.phi u) center)

theorem densityContraction_eq (K : X×X→ᵇℝ) (u : Θ) :
    d.densityContraction K u = 2*(d.densityGenerator K u-d.dotell u) := by
  unfold densityContraction densityGenerator pathHeatDensityGenerator
  ring

theorem centeredContraction_eq (K : X×X→ᵇℝ) (center : ℝ) (u : Θ) :
    d.centeredContraction K center u =
      2*(d.observableGenerator K u+(d.phi u-center)*d.densityGenerator K u-
        d.dotphi u-(d.phi u-center)*d.dotell u) := by
  have h := pathHeat_generators_centered_identity K (d.S u) (d.P u) (d.M u) (d.Q u)
    (d.dotell u) (d.dotphi u) (d.phi u) center
  change d.observableGenerator K u+(d.phi u-center)*d.densityGenerator K u =
    d.dotphi u+(d.phi u-center)*d.dotell u+(1/2:ℝ)*d.centeredContraction K center u at h
  nlinarith only [h]

theorem printed_weighted_integrability
    (μ : Measure Ω) (state : Ω→Θ) (K : X×X→ᵇℝ) (κ : ℝ≥0)
    (hstate : Measurable state) (hK : ‖K‖≤κ) (e : Ω→ℝ)
    (he : Integrable e μ) (hweight : ∀ω,d.weight (state ω)≤e ω) (center : ℝ) :
    Integrable (fun ω=>d.weight (state ω)*d.dotell (state ω)) μ ∧
    Integrable (fun ω=>d.weight (state ω)*d.dotphi (state ω)) μ ∧
    Integrable (fun ω=>d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))) μ ∧
    Integrable (fun ω=>d.weight (state ω)*d.densityContraction K (state ω)) μ ∧
    Integrable (fun ω=>d.weight (state ω)*d.centeredContraction K center (state ω)) μ := by
  have h := d.dominatedData μ state K κ hstate hK e he hweight
  have hdotell := (d.continuous_dotell.measurable.comp hstate).aestronglyMeasurable (μ:=μ)
  have hdotphi := (d.continuous_dotphi.measurable.comp hstate).aestronglyMeasurable (μ:=μ)
  have hiL := pathHeat_integrable_weighted he d.Dt.coe_nonneg h.weight_measurable hdotell
    h.weight_positive h.weight_bound (.of_forall (fun ω=>d.bound_dotell (state ω)))
  have hiP := pathHeat_integrable_weighted he d.Dphi.coe_nonneg h.weight_measurable hdotphi
    h.weight_positive h.weight_bound (.of_forall (fun ω=>d.bound_dotphi (state ω)))
  have hphiL : ∀ᵐω∂μ,|d.phi (state ω)*d.dotell (state ω)|≤(d.B:ℝ)*d.Dt := by
    apply ae_of_all
    intro ω
    rw [abs_mul]
    exact mul_le_mul (d.bound_phi _) (d.bound_dotell _) (abs_nonneg _) d.B.coe_nonneg
  have hiFL := pathHeat_integrable_weighted he (mul_nonneg d.B.coe_nonneg d.Dt.coe_nonneg)
    h.weight_measurable (h.observable_measurable.mul hdotell) h.weight_positive h.weight_bound hphiL
  have hiH := pathHeat_integrable_weighted he h.nonneg_C h.weight_measurable
    h.density_generator_measurable h.weight_positive h.weight_bound h.density_generator_bound
  have hiJ := pathHeat_integrable_weighted he h.nonneg_D h.weight_measurable
    h.observable_generator_measurable h.weight_positive h.weight_bound h.observable_generator_bound
  have hphiH : ∀ᵐω∂μ,|d.phi (state ω)*d.densityGenerator K (state ω)|≤
      (d.B:ℝ)*d.densityBound κ := by
    apply ae_of_all
    intro ω
    rw [abs_mul]
    exact mul_le_mul (d.bound_phi _) (d.densityGenerator_bound K κ hK _) (abs_nonneg _) d.B.coe_nonneg
  have hiFH := pathHeat_integrable_weighted he (mul_nonneg d.B.coe_nonneg h.nonneg_C)
    h.weight_measurable (h.observable_measurable.mul h.density_generator_measurable)
    h.weight_positive h.weight_bound hphiH
  have hiD : Integrable (fun ω=>d.weight (state ω)*d.densityContraction K (state ω)) μ := by
    convert (hiH.sub hiL).const_mul 2 using 1
    funext ω
    rw [d.densityContraction_eq]
    simp only [Pi.sub_apply, Function.comp_apply]
    ring
  have hiC : Integrable (fun ω=>d.weight (state ω)*d.centeredContraction K center (state ω)) μ := by
    convert ((hiJ.add (hiFH.sub (hiH.const_mul center))).sub
      (hiP.add (hiFL.sub (hiL.const_mul center)))).const_mul 2 using 1
    funext ω
    rw [d.centeredContraction_eq]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Function.comp_apply]
    ring
  exact ⟨hiL,hiP,hiFL,hiD,hiC⟩

end PathHeatContinuousSignedSource
end HexagonPaper
