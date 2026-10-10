module
public import HexagonPaper.PathHeatGeneralGaussianEnvelope

@[expose] public section

/-! Exact rearrangement of the same reference probability/counting measure
for conditional finite Gaussian differentiation and common Wiener DCT. -/
noncomputable section
open MeasureTheory
namespace HexagonPaper
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {A B K : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace K]

def pathHeatReferenceReorder : ((A×B)×K)≃ᵐ((A×K)×B) :=
  MeasurableEquiv.prodAssoc.trans ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl A)
    (MeasurableEquiv.prodComm : B×K≃ᵐK×B)).trans MeasurableEquiv.prodAssoc.symm)

@[simp] theorem pathHeatReferenceReorder_apply (ω : (A×B)×K) :
    pathHeatReferenceReorder ω=((ω.1.1,ω.2),ω.1.2) := rfl

theorem pathHeatReferenceReorder_measurePreserving
    (μ : Measure A) (ν : Measure B) (κ : Measure K) [SFinite μ] [SFinite ν] [SFinite κ] :
    MeasurePreserving (pathHeatReferenceReorder (A:=A) (B:=B) (K:=K))
      ((μ.prod ν).prod κ) ((μ.prod κ).prod ν) := by
  have h1 := measurePreserving_prodAssoc μ ν κ
  have h2 := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ:=ν) (ν:=κ))
  have h3 := (measurePreserving_prodAssoc μ κ ν).symm MeasurableEquiv.prodAssoc
  exact h3.comp (h2.comp h1)

theorem pathHeatReferenceReorder_integral
    (μ : Measure A) (ν : Measure B) (κ : Measure K) [SFinite μ] [SFinite ν] [SFinite κ]
    (f : (A×K)×B→ℝ) :
    (∫ω,f ((ω.1.1,ω.2),ω.1.2)∂(μ.prod ν).prod κ)=
      ∫ω,f ω∂(μ.prod κ).prod ν :=
  (pathHeatReferenceReorder_measurePreserving μ ν κ).integral_comp
    pathHeatReferenceReorder.measurableEmbedding f

theorem pathHeatReferenceReorder_integrable_iff
    (μ : Measure A) (ν : Measure B) (κ : Measure K) [SFinite μ] [SFinite ν] [SFinite κ]
    (f : (A×K)×B→ℝ) :
    Integrable (fun ω=>f ((ω.1.1,ω.2),ω.1.2)) ((μ.prod ν).prod κ) ↔
      Integrable f ((μ.prod κ).prod ν) :=
  (pathHeatReferenceReorder_measurePreserving μ ν κ).integrable_comp_emb
    pathHeatReferenceReorder.measurableEmbedding

end HexagonPaper
