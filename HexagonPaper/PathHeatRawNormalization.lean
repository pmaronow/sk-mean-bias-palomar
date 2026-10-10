module
public import HexagonPaper.PathHeatNormalizedLimit
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-! Global normalization after raw numerator and normalizer
differentiation. Auxiliary variables are integrated before this quotient. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem hasDerivAt_pathHeat_expectation_of_raw
    (W F H J : ℝ→Ω→ℝ) (e : Ω→ℝ) (B C D x : ℝ)
    (h : PathHeatDominatedData μ (W x) (F x) (H x) (J x) e B C D)
    (hZ : HasDerivAt (fun u=>pathHeatNormalizer μ (W u))
      (∫ω,W x ω*H x ω∂μ) x)
    (hN : HasDerivAt (fun u=>∫ω,W u ω*F u ω∂μ)
      (∫ω,W x ω*(J x ω+F x ω*H x ω)∂μ) x) :
    HasDerivAt (fun u=>pathHeatExpectation μ (W u) (F u))
      (pathHeatResponse μ (W x) (F x) (H x) (J x)) x := by
  have hp := pathHeat_normalizer_positive h
  have hiJ := pathHeat_integrable_weighted h.integrable_envelope h.nonneg_D
    h.weight_measurable h.observable_generator_measurable h.weight_positive h.weight_bound
    h.observable_generator_bound
  have hiFH := pathHeat_integrable_weighted h.integrable_envelope (mul_nonneg h.nonneg_B h.nonneg_C)
    h.weight_measurable (h.observable_measurable.mul h.density_generator_measurable)
    h.weight_positive h.weight_bound (by
      filter_upwards [h.observable_bound,h.density_generator_bound] with ω hf hh
      change |F x ω*H x ω|≤B*C
      rw [abs_mul]
      exact mul_le_mul hf hh (abs_nonneg _) h.nonneg_B)
  change Integrable (fun ω=>W x ω*(F x ω*H x ω)) μ at hiFH
  have hraw : (∫ω,W x ω*(J x ω+F x ω*H x ω)∂μ)=
      (∫ω,W x ω*J x ω∂μ)+(∫ω,W x ω*(F x ω*H x ω)∂μ) := by
    have he : (fun ω=>W x ω*(J x ω+F x ω*H x ω))=
        fun ω=>W x ω*J x ω+W x ω*(F x ω*H x ω) := by funext ω;ring
    rw [he,integral_add hiJ hiFH]
  have hd := hN.div hZ hp.ne'
  apply hd.congr_deriv
  rw [hraw,pathHeat_response_eq_raw h]
  unfold pathHeatExpectation
  field_simp [hp.ne']
  <;> ring

end HexagonPaper
