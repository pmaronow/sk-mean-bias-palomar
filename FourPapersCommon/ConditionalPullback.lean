module
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

/-! Conditional expectation pulls back along a genuine probability-law
marginal when the conditioning sigma algebra is pulled back with it. -/
noncomputable section
open Set MeasureTheory
namespace FourPapersCommon
variable {Ω Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]

theorem condExp_comp_of_measurePreserving (Q : Measure Ω) (P : Measure Γ)
    [IsProbabilityMeasure Q] [IsProbabilityMeasure P]
    (X : Ω → Γ) (hX : MeasurePreserving X Q P) (m : MeasurableSpace Γ)
    (hm : m ≤ mΓ)
    (F : Γ → ℝ) (hF : @Measurable Γ ℝ mΓ inferInstance F) (hi : Integrable F P) :
    Q[(fun p => F (X p)) | m.comap X] =ᵐ[Q] fun p => (P[F|m]) (X p) := by
  letI : MeasurableSpace Γ := mΓ
  have hXm : @Measurable Ω Γ inferInstance m X := hX.measurable.mono le_rfl hm
  have hFi : Integrable (fun p => F (X p)) Q := hX.integrable_comp_of_integrable hi
  have hGi : Integrable (fun p => (P[F|m]) (X p)) Q :=
    hX.integrable_comp_of_integrable integrable_condExp
  have hGm : StronglyMeasurable[m.comap X] (fun p => (P[F|m]) (X p)) :=
    stronglyMeasurable_condExp.comp_measurable (comap_measurable X)
  have hG : Measurable (P[F|m]) := (stronglyMeasurable_condExp.mono hm).measurable
  have hset (B : Set Γ) (hB : MeasurableSet B) (f : Γ → ℝ) (hf : Measurable f) :
      (∫p in X ⁻¹' B, f (X p) ∂Q) = ∫x in B, f x ∂P := by
    rw [←integral_indicator (hX.measurable hB), ←integral_indicator hB]
    have he : (∫p, (B.indicator f) (X p) ∂Q) = ∫x, B.indicator f x ∂P := by
      rw [←hX.map_eq, integral_map hX.measurable.aemeasurable (hf.indicator hB).aestronglyMeasurable]
    convert he using 1
    apply integral_congr_ae
    exact .of_forall fun p => by
      by_cases hp : X p ∈ B <;> simp [hp]
  symm
  apply ae_eq_condExp_of_forall_setIntegral_eq hXm.comap_le hFi
  · intro A _ _
    exact hGi.integrableOn
  · intro A hA _
    obtain ⟨B, hB, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hA
    rw [hset B (hm B hB) _ hG, hset B (hm B hB) F hF]
    exact setIntegral_condExp hm hi hB
  · exact hGm.aestronglyMeasurable

end FourPapersCommon
