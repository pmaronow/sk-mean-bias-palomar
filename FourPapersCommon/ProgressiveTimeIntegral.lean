module
public import QuantitativePaper.VectorBrownian
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Adaptation of literal Bochner integrals of progressively measurable
processes on nonnegative time, with no adaptation premise on the integral. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set StochasticCalculus
open scoped NNReal
namespace FourPapersCommon
set_option maxHeartbeats 800000
variable {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem stronglyAdapted_nnreal_integral (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (d : ℝ≥0→Ω→E) (hp : IsStronglyProgressive F d) :
    StronglyAdapted F (fun r sample => ∫ s in Ioc 0 r,d s sample ∂nonnegativeLebesgueMeasure) := by
  intro r
  letI : MeasurableSpace Ω := F r
  change StronglyMeasurable (fun sample => ∫ s in Ioc 0 r,
    d s sample ∂nonnegativeLebesgueMeasure)
  let clamp : ℝ≥0→Iic r := fun s => ⟨min s r,mem_Iic.mpr (min_le_right _ _)⟩
  have hclamp : Measurable clamp := (measurable_id.min measurable_const).subtype_mk
  have hsm : StronglyMeasurable (fun z : ℝ≥0×Ω => d (min z.1 r) z.2) :=
    (hp r).comp_measurable ((hclamp.comp measurable_fst).prodMk measurable_snd)
  have hInt := hsm.integral_prod_left' (μ := nonnegativeLebesgueMeasure.restrict (Ioc 0 r))
  have he : (fun sample => ∫ s in Ioc 0 r,d s sample ∂nonnegativeLebesgueMeasure)=
      (fun sample => ∫ s in Ioc 0 r,d (min s r) sample ∂nonnegativeLebesgueMeasure) := by
    funext sample
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    exact congrArg (fun t => d t sample) (min_eq_left hs.2).symm
  rw [he]
  exact hInt

end FourPapersCommon
