module
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

/-! Replace one factor of a finite independent probability law, allowing
the replaced coordinate to have a different measurable space. Every
untouched coordinate is retained jointly through its genuine cast. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators
namespace FourPapersCommon
variable {I : Type*} [Fintype I] {A B : I → Type*}
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]
set_option autoImplicit false
set_option maxHeartbeats 700000

def finiteProbabilityCoordinateReplacement (c : I)
    (e : ∀ i, i ≠ c → A i ≃ᵐ B i) (z : ((i : I) → A i) × B c) :
    (i : I) → B i := by
  classical
  exact fun i => if hi : i = c then cast (congrArg B hi.symm) z.2 else e i hi (z.1 i)

theorem finiteProbabilityCoordinateReplacement_same (c : I)
    (e : ∀ i, i ≠ c → A i ≃ᵐ B i) (z : ((i : I) → A i) × B c) :
    finiteProbabilityCoordinateReplacement c e z c = z.2 := by
  classical
  simp [finiteProbabilityCoordinateReplacement]

theorem finiteProbabilityCoordinateReplacement_other (c : I)
    (e : ∀ i, i ≠ c → A i ≃ᵐ B i) (z : ((i : I) → A i) × B c)
    (i : I) (hi : i ≠ c) :
    finiteProbabilityCoordinateReplacement c e z i = e i hi (z.1 i) := by
  classical
  simp only [finiteProbabilityCoordinateReplacement, dif_neg hi]

theorem measurable_finiteProbabilityCoordinateReplacement (c : I)
    (e : ∀ i, i ≠ c → A i ≃ᵐ B i) :
    Measurable (finiteProbabilityCoordinateReplacement c e) := by
  classical
  apply Measurable.of_eval
  intro i
  by_cases hi : i = c
  · subst i
    simpa only [finiteProbabilityCoordinateReplacement_same] using
      (measurable_snd : Measurable (Prod.snd : ((i : I) → A i) × B c → B c))
  · simpa only [finiteProbabilityCoordinateReplacement_other c e _ i hi, Function.comp_def] using
      (e i hi).measurable.comp ((measurable_pi_apply i).comp measurable_fst)

theorem finiteProbabilityCoordinateReplacement_measurePreserving
    (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : ∀ i, Measure (B i)) [∀ i, IsProbabilityMeasure (ν i)]
    (c : I) (e : ∀ i, i ≠ c → A i ≃ᵐ B i)
    (he : ∀ i (hi : i ≠ c), MeasurePreserving (e i hi) (μ i) (ν i)) :
    MeasurePreserving (finiteProbabilityCoordinateReplacement c e)
      ((Measure.pi μ).prod (ν c)) (Measure.pi ν) := by
  classical
  refine ⟨measurable_finiteProbabilityCoordinateReplacement c e, ?_⟩
  apply (Measure.pi_eq (μ := ν) ?_).symm
  intro s hs
  let t : ∀ i, Set (A i) := fun i => if hi : i = c then univ else (e i hi) ⁻¹' s i
  have hpre : (finiteProbabilityCoordinateReplacement c e) ⁻¹' (univ.pi s) =
      (univ.pi t) ×ˢ s c := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : i = c
        · simp only [t, dif_pos hi, mem_univ]
        · simpa only [t, dif_neg hi, mem_preimage,
            finiteProbabilityCoordinateReplacement_other c e z i hi] using hz i
      · simpa only [finiteProbabilityCoordinateReplacement_same] using hz c
    · rintro ⟨hz, hc⟩ i
      by_cases hi : i = c
      · subst i
        simpa only [finiteProbabilityCoordinateReplacement_same] using hc
      · simpa only [t, dif_neg hi, mem_preimage,
          finiteProbabilityCoordinateReplacement_other c e z i hi] using hz i
  rw [Measure.map_apply (measurable_finiteProbabilityCoordinateReplacement c e)
    (MeasurableSet.univ_pi hs), hpre, Measure.prod_prod, Measure.pi_pi]
  have htc : μ c (t c) = 1 := by simp only [t, dif_pos rfl, measure_univ]
  have hti (i : I) (hi : i ≠ c) : μ i (t i) = ν i (s i) := by
    simp only [t, dif_neg hi]
    rw [← (he i hi).map_eq, Measure.map_apply (e i hi).measurable (hs i)]
  have hp : (∏ i, μ i (t i)) = ∏ i ∈ Finset.univ.erase c, ν i (s i) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c), htc, mul_one]
    apply Finset.prod_congr rfl
    intro i hi
    exact hti i (Finset.mem_erase.mp hi).1
  rw [hp, Finset.prod_erase_mul _ _ (Finset.mem_univ c)]

theorem integral_finiteProbabilityCoordinateReplacement
    (μ : ∀ i, Measure (A i)) [∀ i, IsProbabilityMeasure (μ i)]
    (ν : ∀ i, Measure (B i)) [∀ i, IsProbabilityMeasure (ν i)]
    (c : I) (e : ∀ i, i ≠ c → A i ≃ᵐ B i)
    (he : ∀ i (hi : i ≠ c), MeasurePreserving (e i hi) (μ i) (ν i))
    (F : ((i : I) → B i) → ℝ) (hF : Integrable F (Measure.pi ν)) :
    (∫ x, ∫ y, F (finiteProbabilityCoordinateReplacement c e (x,y)) ∂ν c
      ∂Measure.pi μ) = ∫ z, F z ∂Measure.pi ν := by
  let g := finiteProbabilityCoordinateReplacement c e
  have hp : MeasurePreserving g ((Measure.pi μ).prod (ν c)) (Measure.pi ν) :=
    finiteProbabilityCoordinateReplacement_measurePreserving μ ν c e he
  have hm : AEStronglyMeasurable F (((Measure.pi μ).prod (ν c)).map g) := by
    rw [hp.map_eq]
    exact hF.aestronglyMeasurable
  have hi : Integrable (F ∘ g) ((Measure.pi μ).prod (ν c)) := by
    apply (integrable_map_measure hm hp.measurable.aemeasurable).mp
    rw [hp.map_eq]
    exact hF
  change (∫ x, ∫ y, (F ∘ g) (x,y) ∂ν c ∂Measure.pi μ) = _
  rw [← integral_prod _ hi]
  calc
    _ = ∫ z, F z ∂(((Measure.pi μ).prod (ν c)).map g) :=
      (integral_map hp.measurable.aemeasurable hm).symm
    _ = _ := by rw [hp.map_eq]

end FourPapersCommon
