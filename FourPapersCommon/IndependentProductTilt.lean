module
public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Exponential tilting by an additive independent potential preserves the
product structure. This is an exact normalized measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
set_option maxHeartbeats 300000

theorem tilted_prod_add (P : Measure A) (Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : A → ℝ) (g : B → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun x => Real.exp (f x)) P)
    (hgi : Integrable (fun y => Real.exp (g y)) Q) :
    (P.prod Q).tilted (fun z => f z.1 + g z.2) =
      (P.tilted f).prod (Q.tilted g) := by
  have hp := integral_exp_pos hfi
  have hq := integral_exp_pos hgi
  have he : (∫ z : A × B, Real.exp (f z.1 + g z.2) ∂P.prod Q) =
      (∫ x, Real.exp (f x) ∂P) * (∫ y, Real.exp (g y) ∂Q) := by
    simp_rw [Real.exp_add]
    exact integral_prod_mul (fun x => Real.exp (f x)) (fun y => Real.exp (g y))
  rw [Measure.tilted, Measure.tilted, Measure.tilted,
    prod_withDensity ((hf.exp).div_const _).ennreal_ofReal
      ((hg.exp).div_const _).ennreal_ofReal, he]
  congr 1
  funext z
  rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hp.le), Real.exp_add]
  congr 1
  field_simp

theorem tilted_prod_add_map_fst (P : Measure A) (Q : Measure B)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : A → ℝ) (g : B → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable (fun x => Real.exp (f x)) P)
    (hgi : Integrable (fun y => Real.exp (g y)) Q) :
    ((P.prod Q).tilted (fun z => f z.1 + g z.2)).map Prod.fst = P.tilted f := by
  haveI := isProbabilityMeasure_tilted hfi
  haveI := isProbabilityMeasure_tilted hgi
  rw [tilted_prod_add P Q f g hf hg hfi hgi]
  exact measurePreserving_fst.map_eq

end FourPapersCommon
