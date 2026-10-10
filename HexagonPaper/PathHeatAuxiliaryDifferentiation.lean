module
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

/-! Local integration of actual conditional finite Price derivatives.
These hypotheses are intermediate finite-mesh data, to be discharged by
the real finite Gaussian calculation in the source-facing path theorem.
The raw numerator and normalizer are integrated before taking their quotient. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω]

structure PathHeatAuxiliaryRawData (ν : Measure Ω) (f d : ℝ→Ω→ℝ)
    (S : Set ℝ) (a : ℝ) (bound : Ω→ℝ) : Prop where
  measurable : ∀z∈S,AEStronglyMeasurable (f z) ν
  integrable : Integrable (f a) ν
  derivative_measurable : AEStronglyMeasurable (d a) ν
  derivative_bound : ∀ω,∀z∈S,‖d z ω‖≤bound ω
  bound_integrable : Integrable bound ν
  conditional_derivative : ∀ω,∀z∈S,HasDerivAt (fun u=>f u ω) (d z ω) z

theorem hasDerivAt_pathHeat_auxiliary_raw_integral
    (ν : Measure Ω) (f d : ℝ→Ω→ℝ) (S : Set ℝ) (a : ℝ) (bound : Ω→ℝ)
    (hS : S∈𝓝 a) (h : PathHeatAuxiliaryRawData ν f d S a bound) :
    Integrable (d a) ν ∧
      HasDerivAt (fun z=>∫ω,f z ω∂ν) (∫ω,d a ω∂ν) a := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le hS
  · filter_upwards [hS] with z hz
    exact h.measurable z hz
  · exact h.integrable
  · exact h.derivative_measurable
  · exact .of_forall fun ω=>h.derivative_bound ω
  · exact h.bound_integrable
  · exact .of_forall fun ω=>h.conditional_derivative ω

/-- The true globally normalized finite-mesh expectation. In particular,
there is a single global normalizer after auxiliary integration. -/
theorem hasDerivAt_pathHeat_auxiliary_global_quotient
    (ν : Measure Ω) (N Z dN dZ : ℝ→Ω→ℝ)
    (S : Set ℝ) (a : ℝ) (bN bZ : Ω→ℝ) (hS : S∈𝓝 a)
    (hN : PathHeatAuxiliaryRawData ν N dN S a bN)
    (hZ : PathHeatAuxiliaryRawData ν Z dZ S a bZ)
    (hZ0 : (∫ω,Z a ω∂ν)≠0) :
    HasDerivAt (fun z=>(∫ω,N z ω∂ν)/(∫ω,Z z ω∂ν))
      (((∫ω,dN a ω∂ν)*(∫ω,Z a ω∂ν)-
        (∫ω,N a ω∂ν)*(∫ω,dZ a ω∂ν))/(∫ω,Z a ω∂ν)^2) a :=
  (hasDerivAt_pathHeat_auxiliary_raw_integral ν N dN S a bN hS hN).2.div
    (hasDerivAt_pathHeat_auxiliary_raw_integral ν Z dZ S a bZ hS hZ).2 hZ0

theorem hasDerivAt_pathHeat_auxiliary_log_normalizer
    (ν : Measure Ω) (Z dZ : ℝ→Ω→ℝ)
    (S : Set ℝ) (a : ℝ) (bZ : Ω→ℝ) (hS : S∈𝓝 a)
    (hZ : PathHeatAuxiliaryRawData ν Z dZ S a bZ)
    (hZ0 : (∫ω,Z a ω∂ν)≠0) :
    HasDerivAt (fun z=>Real.log (∫ω,Z z ω∂ν))
      ((∫ω,dZ a ω∂ν)/(∫ω,Z a ω∂ν)) a :=
  (hasDerivAt_pathHeat_auxiliary_raw_integral ν Z dZ S a bZ hS hZ).2.log hZ0

end HexagonPaper
