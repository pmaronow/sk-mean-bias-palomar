module
public import Mathlib.MeasureTheory.Measure.Prod

@[expose] public section

/-! The actual interchange of four independent finite-measure coordinates. -/
noncomputable section
open MeasureTheory
namespace FourPapersCommon
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

theorem measurePreserving_product_interchange
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    MeasurePreserving (fun p : (A×B)×(C×D) => ((p.1.1,p.2.1),(p.1.2,p.2.2)))
      ((μ.prod ν).prod (ρ.prod τ)) ((μ.prod ρ).prod (ν.prod τ)) := by
  have h1 := measurePreserving_prodAssoc μ ν (ρ.prod τ)
  have h2 := (MeasurePreserving.id μ).prod
    ((measurePreserving_prodAssoc ν ρ τ).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id μ).prod
    ((Measure.measurePreserving_swap (μ:=ν) (ν:=ρ)).prod (MeasurePreserving.id τ))
  have h4 := (MeasurePreserving.id μ).prod (measurePreserving_prodAssoc ρ ν τ)
  have h5 := (measurePreserving_prodAssoc μ ρ (ν.prod τ)).symm MeasurableEquiv.prodAssoc
  convert h5.comp (h4.comp (h3.comp (h2.comp h1))) using 1
  rfl

theorem map_product_interchange
    (μ : Measure A) (ν : Measure B) (ρ : Measure C) (τ : Measure D)
    [SFinite μ] [SFinite ν] [SFinite ρ] [SFinite τ] :
    ((μ.prod ν).prod (ρ.prod τ)).map
      (fun p : (A×B)×(C×D) => ((p.1.1,p.2.1),(p.1.2,p.2.2))) =
      (μ.prod ρ).prod (ν.prod τ) :=
  (measurePreserving_product_interchange μ ν ρ τ).map_eq

end FourPapersCommon
