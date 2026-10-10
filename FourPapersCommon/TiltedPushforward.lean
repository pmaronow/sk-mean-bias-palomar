module
public import FourPapersCommon.CompProdComapMap
public import Mathlib.MeasureTheory.Measure.Tilted

@[expose] public section

/-! Exact pushforward of an exponential tilt pulled back through an actual
measurable sample map. The normalizer is transported by the Bochner
integral map theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

theorem map_tilted_pullback (P : Measure A) (j : A→B) (hj : Measurable j)
    (f : B→ℝ) (hf : Measurable f) :
    (P.tilted (f ∘ j)).map j = (P.map j).tilted f := by
  have he := integral_map hj.aemeasurable hf.exp.aestronglyMeasurable (μ:=P)
  rw [Measure.tilted,Measure.tilted,he]
  exact map_withDensity_pullback P j hj
    (fun y => ENNReal.ofReal (Real.exp (f y)/(∫x,Real.exp (f (j x)) ∂P)))
    (hf.exp.div_const _).ennreal_ofReal

end FourPapersCommon
