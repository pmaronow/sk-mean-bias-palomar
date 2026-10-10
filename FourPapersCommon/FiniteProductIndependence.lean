module
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! Tensorizing genuine independence across independent coordinates and
adjoining independent initial randomness. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace FourPapersCommon

theorem indepFun_finiteProduct {I Ω A B : Type*} [Fintype I]
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    (P : I → Measure Ω) [∀ i, IsProbabilityMeasure (P i)]
    (f : I → Ω → A) (g : I → Ω → B)
    (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i))
    (hI : ∀ i, IndepFun (f i) (g i) (P i)) :
    IndepFun (fun sample : I → Ω => fun i => f i (sample i))
      (fun sample : I → Ω => fun i => g i (sample i)) (Measure.pi P) := by
  let F : (I → Ω) → (I → A) := fun sample i => f i (sample i)
  let G : (I → Ω) → (I → B) := fun sample i => g i (sample i)
  let H : (I → Ω) → (I → A × B) := fun sample i => (f i (sample i),g i (sample i))
  have hF : Measurable F := Measurable.of_eval fun i => (hf i).comp (measurable_pi_apply i)
  have hG : Measurable G := Measurable.of_eval fun i => (hg i).comp (measurable_pi_apply i)
  have hH : Measurable H := Measurable.of_eval fun i =>
    ((hf i).prodMk (hg i)).comp (measurable_pi_apply i)
  have hp (i : I) : (P i).map (fun sample => (f i sample,g i sample)) =
      ((P i).map (f i)).prod ((P i).map (g i)) :=
    (hI i).map_prod_eq_prod_map_map (hf i).aemeasurable (hg i).aemeasurable
  have hmap : (fun sample : I → Ω => (F sample,G sample)) =
      (MeasurableEquiv.arrowProdEquivProdArrow A B I) ∘ H := rfl
  apply (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hG.aemeasurable).mpr
  rw [hmap,← Measure.map_map (MeasurableEquiv.arrowProdEquivProdArrow A B I).measurable hH,
    Measure.pi_map_pi (fun i => ((hf i).prodMk (hg i)).aemeasurable)]
  simp only [hp]
  rw [(measurePreserving_arrowProdEquivProdArrow A B I
    (fun i => (P i).map (f i)) (fun i => (P i).map (g i))).map_eq]
  unfold F G
  rw [Measure.pi_map_pi (fun i => (hf i).aemeasurable),
    Measure.pi_map_pi (fun i => (hg i).aemeasurable)]

theorem indepFun_adjoin_initial {Ω A B C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (P : Measure Ω) (Q : Measure C) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (f : Ω → A) (g : Ω → B) (hf : Measurable f) (hg : Measurable g)
    (hI : IndepFun f g P) :
    IndepFun (fun sample : C × Ω => f sample.2)
      (fun sample : C × Ω => (sample.1,g sample.2)) (Q.prod P) := by
  let PA := P.map f
  let PB := P.map g
  let E : C × (A × B) ≃ᵐ A × (C × B) :=
    (MeasurableEquiv.prodAssoc : ((C × A) × B) ≃ᵐ C × (A × B)).symm.trans
      (((MeasurableEquiv.prodComm : C × A ≃ᵐ A × C).prodCongr
        (MeasurableEquiv.refl B)).trans MeasurableEquiv.prodAssoc)
  have hE : MeasurePreserving E (Q.prod (PA.prod PB)) (PA.prod (Q.prod PB)) := by
    exact ((measurePreserving_prodAssoc PA Q PB).comp
      ((Measure.measurePreserving_swap (μ := Q) (ν := PA)).prod (MeasurePreserving.id PB))).comp
        (measurePreserving_prodAssoc Q PA PB).symm
  have hpair : (fun sample : C × Ω => (f sample.2,(sample.1,g sample.2))) =
      E ∘ Prod.map id (fun x => (f x,g x)) := rfl
  have hF : Measurable (fun sample : C × Ω => f sample.2) := hf.comp measurable_snd
  have hG : Measurable (fun sample : C × Ω => (sample.1,g sample.2)) :=
    measurable_fst.prodMk (hg.comp measurable_snd)
  apply (indepFun_iff_map_prod_eq_prod_map_map hF.aemeasurable hG.aemeasurable).mpr
  rw [hpair,← Measure.map_map E.measurable (measurable_id.prodMap (hf.prodMk hg)),
    ← Measure.map_prod_map Q P measurable_id (hf.prodMk hg),Measure.map_id,
    hI.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,hE.map_eq]
  change PA.prod (Q.prod PB) = _
  have hfmap : (Q.prod P).map (fun sample : C × Ω => f sample.2) = PA := by
    rw [← Function.comp_def,← Measure.map_map hf measurable_snd,Measure.map_snd_prod,
      measure_univ,one_smul]
  have hgmap : (Q.prod P).map (fun sample : C × Ω => (sample.1,g sample.2)) = Q.prod PB := by
    change (Q.prod P).map (Prod.map id g) = _
    rw [← Measure.map_prod_map Q P measurable_id hg,Measure.map_id]
  rw [hfmap,hgmap]

end FourPapersCommon
