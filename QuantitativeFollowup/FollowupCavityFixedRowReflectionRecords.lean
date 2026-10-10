module
public import QuantitativeFollowup.FollowupCavityFixedRowReflectionCascade

@[expose] public section

/-! The permutation of every retained field and terminal spin transports
the full normalized Gaussian genealogy, including the outer disorder tilt. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open FourPapersCommon OverlapPaper SpinGlass.AT FiniteTerminalGenealogy
namespace QuantitativeFollowup
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
set_option backward.isDefEq.respectTransparency false
variable {S I J : Type} [Fintype S] [Fintype I] [Fintype J] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]

@[reducible] def cavityPermuteRecords (e : S ≃ S) :
    {j : ℕ} → (T : FiniteTerminalGenealogy j) →
      Records (FiniteStateField S) S T → Records (FiniteStateField S) S T
  | _, .leaf => e
  | _, .advance T => Prod.map (cavityStatePermutation e) (cavityPermuteRecords e T)
  | _, .fork T U => Prod.map (cavityPermuteRecords e T) (cavityPermuteRecords e U)

theorem measurable_cavityPermuteRecords (e : S ≃ S) {j : ℕ}
    (T : FiniteTerminalGenealogy j) : Measurable (cavityPermuteRecords e T) := by
  induction T with
  | leaf => exact measurable_of_countable _
  | advance T ih => exact (cavityStatePermutation e).continuous.measurable.prodMap ih
  | fork T U ihT ihU => exact ihT.prodMap ihU

private theorem comp_comap_initial {A B C D : Type} [MeasurableSpace A]
    [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace D]
    (κ : Kernel A B) (η : Kernel B C) (f : D → A) (hf : Measurable f) :
    (η ∘ₖ κ).comap f hf = η ∘ₖ (κ.comap f hf) := by
  rw [←Kernel.comp_deterministic_eq_comap,
    ←Kernel.comp_deterministic_eq_comap, Kernel.comp_assoc]

theorem cavityRecordKernel_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z))
    {j : ℕ} (T : FiniteTerminalGenealogy j) :
    (finiteCascadeTreeRecordKernel V a L T).map (cavityPermuteRecords e T) =
      (finiteCascadeTreeRecordKernel V a L T).comap
        (cavityStatePermutation e) (cavityStatePermutation e).continuous.measurable := by
  induction T with
  | leaf => exact cavityGibbsKernel_statePermutation e V hV
  | @advance j T ih =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      change ((_ ×ₖ _) ∘ₖ _).map
          (Prod.map (cavityStatePermutation e) (cavityPermuteRecords e T)) =
        ((_ ×ₖ _) ∘ₖ _).comap _ _
      rw [Kernel.map_comp, ←Kernel.map_prod_map _ _
        (cavityStatePermutation e).continuous.measurable (measurable_cavityPermuteRecords e T),
        ih, Kernel.id_map (cavityStatePermutation e).continuous.measurable,
        ←Kernel.id_comap (cavityStatePermutation e).continuous.measurable,
        ←Kernel.comap_prod, ←Kernel.comp_map _ _ (cavityStatePermutation e).continuous.measurable,
        cavityGaussianCascadeKernel_statePermutation e V hV a ha L A hL j,
        ←comp_comap_initial]
  | fork T U ihT ihU =>
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
      haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L U
      change (_ ×ₖ _).map
          (Prod.map (cavityPermuteRecords e T) (cavityPermuteRecords e U)) =
        (_ ×ₖ _).comap _ _
      rw [←Kernel.map_prod_map _ _ (measurable_cavityPermuteRecords e T)
        (measurable_cavityPermuteRecords e U), ihT, ihU, ←Kernel.comap_prod]

theorem cavityGaussianNormalizer_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z))
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (B : FiniteStateGaussianInput J ≃ₗᵢ[ℝ] FiniteStateGaussianInput J)
    (hR : ∀z, cavityStatePermutation e (R z) = R (B z))
    (s : ℝ) (j : ℕ) (H : FiniteStateField S) :
    finiteCascadeTreeGaussianNormalizer V a L s j R (cavityStatePermutation e H) =
      finiteCascadeTreeGaussianNormalizer V a L s j R H := by
  unfold finiteCascadeTreeGaussianNormalizer
  rw [←cavityGaussianRaw_statePermutation _ B R hR H,
    integral_map (cavityStatePermutation e).continuous.measurable.aemeasurable
      (((contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable.const_mul s).exp.aestronglyMeasurable)]
  congr 1
  funext Q
  rw [cavityGaussianCascade_statePermutation e V hV a ha L A hL]

private theorem kernel_comp_map_measure {X Y Z : Type} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure X) (κ : Kernel Y Z)
    (f : X → Y) (hf : Measurable f) :
    κ ∘ₘ (μ.map f) = (κ.comap f hf) ∘ₘ μ := by
  ext B hB
  rw [Measure.bind_apply hB κ.aemeasurable,
    Measure.bind_apply hB (Kernel.aemeasurable _),
    lintegral_map (κ.measurable_coe hB) hf]
  rfl

theorem cavityGaussianJointLaw_statePermutation (e : S ≃ S) (V : S → ℝ)
    (hV : ∀s, V (e s) = V s) (a : ℕ → ℝ) (ha : ∀j, 0 ≤ a j)
    (L : ℕ → FiniteStateGaussianInput I →L[ℝ] FiniteStateField S)
    (A : ℕ → FiniteStateGaussianInput I ≃ₗᵢ[ℝ] FiniteStateGaussianInput I)
    (hL : ∀j z, cavityStatePermutation e (L j z) = L j (A j z))
    (R : FiniteStateGaussianInput J →L[ℝ] FiniteStateField S)
    (B : FiniteStateGaussianInput J ≃ₗᵢ[ℝ] FiniteStateGaussianInput J)
    (hR : ∀z, cavityStatePermutation e (R z) = R (B z))
    (s : ℝ) {j : ℕ} (T : FiniteTerminalGenealogy j) (H : FiniteStateField S) :
    (finiteCascadeTreeGaussianJointLaw V a L s T R H).map
        (Prod.map (cavityStatePermutation e) (cavityPermuteRecords e T)) =
      finiteCascadeTreeGaussianJointLaw V a L s T R (cavityStatePermutation e H) := by
  haveI := isMarkovKernel_finiteCascadeTreeRecordKernel V a ha L T
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R H)
  haveI := isProbabilityMeasure_tilted
    (integrable_exp_finiteCascadeTreeGaussianInitial V a ha L s j R (cavityStatePermutation e H))
  unfold finiteCascadeTreeGaussianJointLaw
  rw [Measure.compProd_eq_comp_prod, Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ ((cavityStatePermutation e).continuous.measurable.prodMap
      (measurable_cavityPermuteRecords e T)),
    ←Kernel.map_prod_map _ _ (cavityStatePermutation e).continuous.measurable
      (measurable_cavityPermuteRecords e T),
    cavityRecordKernel_statePermutation e V hV a ha L A hL T,
    Kernel.id_map (cavityStatePermutation e).continuous.measurable,
    ←Kernel.id_comap (cavityStatePermutation e).continuous.measurable,
    ←Kernel.comap_prod, ←kernel_comp_map_measure]
  congr 1
  exact cavityGaussianStepLaw_statePermutation _ B R hR s _
    (contDiff_one_finiteStateGaussianTerminalCascade V a ha L j).continuous.measurable
    (cavityGaussianCascade_statePermutation e V hV a ha L A hL j) H

end QuantitativeFollowup
