module
public import HexagonPaper.PathHeatPrintedResponseIntegrability

@[expose] public section

/-! The manuscript's exact normalized covariance and centered signed
measure formula, derived from the true uncentered generators. All scalar
integrals are justified by the actual source/envelope integrability leaf. -/
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

theorem normalized_densityGenerator_printed
    (μ : Measure Ω) (state : Ω→Θ) (K : X×X→ᵇℝ) (κ : ℝ≥0)
    (hstate : Measurable state) (hK : ‖K‖≤κ) (e : Ω→ℝ)
    (he : Integrable e μ) (hweight : ∀ω,d.weight (state ω)≤e ω) :
    pathHeatExpectation μ (fun ω=>d.weight (state ω))
      (fun ω=>d.densityGenerator K (state ω)) =
    pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotell (state ω))+
      (1/2:ℝ)*pathHeatExpectation μ (fun ω=>d.weight (state ω))
        (fun ω=>d.densityContraction K (state ω)) := by
  obtain ⟨hiL,_,_,hiD,_⟩ := d.printed_weighted_integrability
    μ state K κ hstate hK e he hweight 0
  have hfun : (fun ω=>d.weight (state ω)*d.densityGenerator K (state ω)) =
      (fun ω=>d.weight (state ω)*d.dotell (state ω)+
        (1/2:ℝ)*(d.weight (state ω)*d.densityContraction K (state ω))) := by
    funext ω
    rw [d.densityContraction_eq]
    ring
  unfold pathHeatExpectation
  rw [hfun,integral_add hiL (hiD.const_mul (1/2:ℝ)),integral_const_mul]
  ring

theorem normalized_response_printed
    (μ : Measure Ω) (state : Ω→Θ) (K : X×X→ᵇℝ) (κ : ℝ≥0)
    (hstate : Measurable state) (hK : ‖K‖≤κ) (e : Ω→ℝ)
    (he : Integrable e μ) (hweight : ∀ω,d.weight (state ω)≤e ω) :
    pathHeatResponse μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
      (fun ω=>d.densityGenerator K (state ω)) (fun ω=>d.observableGenerator K (state ω)) =
    pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotphi (state ω))+
      (pathHeatExpectation μ (fun ω=>d.weight (state ω))
          (fun ω=>d.phi (state ω)*d.dotell (state ω))-
        pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))*
          pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotell (state ω)))+
      (1/2:ℝ)*pathHeatExpectation μ (fun ω=>d.weight (state ω))
        (fun ω=>d.centeredContraction K
          (pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω)))
          (state ω)) := by
  let c := pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
  obtain ⟨hiL,hiP,hiFL,_,hiC⟩ := d.printed_weighted_integrability
    μ state K κ hstate hK e he hweight c
  have hfun : (fun ω=>d.weight (state ω)*
      (d.observableGenerator K (state ω)+(d.phi (state ω)-c)*d.densityGenerator K (state ω))) =
      (fun ω=>d.weight (state ω)*d.dotphi (state ω)+
        (d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))-
          c*(d.weight (state ω)*d.dotell (state ω)))+
        (1/2:ℝ)*(d.weight (state ω)*d.centeredContraction K c (state ω))) := by
    funext ω
    rw [d.centeredContraction_eq]
    ring
  change (∫ω,d.weight (state ω)*
      (d.observableGenerator K (state ω)+(d.phi (state ω)-c)*d.densityGenerator K (state ω))∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω)) =
      (∫ω,d.weight (state ω)*d.dotphi (state ω)∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω))+
      ((∫ω,d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω))-
        c*((∫ω,d.weight (state ω)*d.dotell (state ω)∂μ)/
          pathHeatNormalizer μ (fun ω=>d.weight (state ω))))+
      (1/2:ℝ)*((∫ω,d.weight (state ω)*d.centeredContraction K c (state ω)∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω)))
  have hiMixed : Integrable (fun ω=>
      d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))-
        c*(d.weight (state ω)*d.dotell (state ω))) μ := hiFL.sub (hiL.const_mul c)
  have hiSum : Integrable (fun ω=>d.weight (state ω)*d.dotphi (state ω)+
      (d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))-
        c*(d.weight (state ω)*d.dotell (state ω)))) μ := hiP.add hiMixed
  rw [hfun,integral_add hiSum (hiC.const_mul (1/2:ℝ)),
    integral_add hiP hiMixed,integral_sub hiFL (hiL.const_mul c),
    integral_const_mul,integral_const_mul]
  ring

end PathHeatContinuousSignedSource
end HexagonPaper
