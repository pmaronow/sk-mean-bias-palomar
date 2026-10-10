module
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Product integrability for bounded jointly measurable families, with
one or two actual finite-measure integrations. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {Q I S : Type*} [MeasurableSpace Q] [MeasurableSpace I] [MeasurableSpace S]

theorem integrable_bounded_integral_family (ν : Measure Q) (P : Measure S)
    [IsFiniteMeasure ν] [IsFiniteMeasure P] (F : Q→S→ℝ)
    (hF : Measurable (Function.uncurry F)) (B : ℝ) (hb : ∀q s,‖F q s‖≤B) :
    Integrable (fun q=>∫s,F q s ∂P) ν :=
  ((integrable_const B).mono' hF.aestronglyMeasurable
    (.of_forall fun z=>hb z.1 z.2)).integral_prod_left

theorem integrable_bounded_double_integral_family (ν : Measure Q) (η : Measure I) (P : Measure S)
    [IsFiniteMeasure ν] [IsFiniteMeasure η] [IsFiniteMeasure P] (F : Q→I→S→ℝ)
    (hF : Measurable (fun z : (Q×I)×S=>F z.1.1 z.1.2 z.2))
    (B : ℝ) (hb : ∀q i s,‖F q i s‖≤B) :
    Integrable (fun q=>∫i,∫s,F q i s ∂P ∂η) ν :=
  (integrable_bounded_integral_family (ν.prod η) P (fun qi s=>F qi.1 qi.2 s)
    hF B (fun qi s=>hb qi.1 qi.2 s)).integral_prod_left

end FourPapersCommon
