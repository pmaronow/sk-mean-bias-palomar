module
public import HexagonPaper.PathHeatSectionwisePrintedIntegrability

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
variable {X Z E K Ω : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [CompactSpace X] [SecondCountableTopology X]
  [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K] [MeasurableSpace Ω]
local instance instSectionwisePrintedResponsePathMeasurable : MeasurableSpace C(X,ℝ) := borel C(X,ℝ)
local instance instSectionwisePrintedResponsePathBorel : BorelSpace C(X,ℝ) := ⟨rfl⟩

namespace PathHeatSectionwiseSignedSource
variable (d : PathHeatSectionwiseSignedSource Z E K X)

theorem normalized_densityGenerator_printed
    (μ : Measure Ω) (state : Ω→Z×((E×K)×C(X,ℝ))) (kernel : X×X→ᵇℝ)
    (hstate : Measurable state) (e : Ω→ℝ) (C D : ℝ)
    (h : PathHeatDominatedData μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
      (fun ω=>d.densityGenerator kernel (state ω)) (fun ω=>d.observableGenerator kernel (state ω))
      e d.B C D) :
    pathHeatExpectation μ (fun ω=>d.weight (state ω))
      (fun ω=>d.densityGenerator kernel (state ω)) =
    pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotell (state ω))+
      (1/2:ℝ)*pathHeatExpectation μ (fun ω=>d.weight (state ω))
        (fun ω=>d.densityContraction kernel (state ω)) := by
  obtain ⟨hiL,_,_,hiD,_⟩ := d.printed_weighted_integrability
    μ state kernel hstate e C D h 0
  have hfun : (fun ω=>d.weight (state ω)*d.densityGenerator kernel (state ω)) =
      (fun ω=>d.weight (state ω)*d.dotell (state ω)+
        (1/2:ℝ)*(d.weight (state ω)*d.densityContraction kernel (state ω))) := by
    funext ω
    rw [d.densityContraction_eq]
    ring
  unfold pathHeatExpectation
  rw [hfun,integral_add hiL (hiD.const_mul (1/2:ℝ)),integral_const_mul]
  ring

theorem normalized_response_printed
    (μ : Measure Ω) (state : Ω→Z×((E×K)×C(X,ℝ))) (kernel : X×X→ᵇℝ)
    (hstate : Measurable state) (e : Ω→ℝ) (C D : ℝ)
    (h : PathHeatDominatedData μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
      (fun ω=>d.densityGenerator kernel (state ω)) (fun ω=>d.observableGenerator kernel (state ω))
      e d.B C D) :
    pathHeatResponse μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
      (fun ω=>d.densityGenerator kernel (state ω)) (fun ω=>d.observableGenerator kernel (state ω)) =
    pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotphi (state ω))+
      (pathHeatExpectation μ (fun ω=>d.weight (state ω))
          (fun ω=>d.phi (state ω)*d.dotell (state ω))-
        pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))*
          pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.dotell (state ω)))+
      (1/2:ℝ)*pathHeatExpectation μ (fun ω=>d.weight (state ω))
        (fun ω=>d.centeredContraction kernel
          (pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω)))
          (state ω)) := by
  let c := pathHeatExpectation μ (fun ω=>d.weight (state ω)) (fun ω=>d.phi (state ω))
  obtain ⟨hiL,hiP,hiFL,_,hiC⟩ := d.printed_weighted_integrability
    μ state kernel hstate e C D h c
  have hfun : (fun ω=>d.weight (state ω)*
      (d.observableGenerator kernel (state ω)+(d.phi (state ω)-c)*d.densityGenerator kernel (state ω))) =
      (fun ω=>d.weight (state ω)*d.dotphi (state ω)+
        (d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))-
          c*(d.weight (state ω)*d.dotell (state ω)))+
        (1/2:ℝ)*(d.weight (state ω)*d.centeredContraction kernel c (state ω))) := by
    funext ω
    rw [d.centeredContraction_eq]
    ring
  change (∫ω,d.weight (state ω)*
      (d.observableGenerator kernel (state ω)+(d.phi (state ω)-c)*d.densityGenerator kernel (state ω))∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω)) =
      (∫ω,d.weight (state ω)*d.dotphi (state ω)∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω))+
      ((∫ω,d.weight (state ω)*(d.phi (state ω)*d.dotell (state ω))∂μ)/
        pathHeatNormalizer μ (fun ω=>d.weight (state ω))-
        c*((∫ω,d.weight (state ω)*d.dotell (state ω)∂μ)/
          pathHeatNormalizer μ (fun ω=>d.weight (state ω))))+
      (1/2:ℝ)*((∫ω,d.weight (state ω)*d.centeredContraction kernel c (state ω)∂μ)/
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

end PathHeatSectionwiseSignedSource
end HexagonPaper
