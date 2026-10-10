module
public import QuantitativePaper.SmoothIntegral

@[expose] public section

/-! Local parameter smoothness of genuine integrals on open domains.
Actual derivatives are dominated on a neighbourhood contained in the domain;
no global extension across singular parameter values is needed. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} [MeasurableSpace α]
set_option maxHeartbeats 1400000

theorem contDiffOn_integral_of_dominated_derivatives {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (N : ℕ) (μ : Measure α) (f : E → α → F) (U : Set E) (hU : IsOpen U)
    (hf : ∀ z, ContDiffOn ℝ N (fun x => f x z) U)
    (hmeas : ∀ j, j ≤ N → ∀ x ∈ U, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f y z) x) μ)
    (hbound : ∀ x ∈ U, ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ B : ℕ → α → ℝ,
      (∀ j, j ≤ N → Integrable (B j) μ) ∧
      ∀ j, j ≤ N → ∀ y ∈ s, ∀ z, ‖iteratedFDeriv ℝ j (fun u => f u z) y‖ ≤ B j z) :
    ContDiffOn ℝ N (fun x => ∫ z, f x z ∂μ) U := by
  induction N generalizing F with
  | zero =>
    apply contDiffOn_zero.mpr
    intro x hx
    obtain ⟨s, hs, hsu, B, hBi, hB⟩ := hbound x hx
    have hm (y : E) (hy : y ∈ U) : AEStronglyMeasurable (f y) μ := by
      have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
        (hmeas 0 (le_refl _) y hy)
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        LinearIsometryEquiv.apply_symm_apply] using hh
    have hc : ContinuousAt (fun x => ∫ z, f x z ∂μ) x :=
      continuousAt_of_dominated
        (Filter.Eventually.mono hs fun y hy => hm y (hsu hy))
        (Filter.Eventually.mono hs fun y hy => .of_forall fun z => by
          simpa only [norm_iteratedFDeriv_zero] using hB 0 (le_refl _) y hy z)
        (hBi 0 (le_refl _))
        (.of_forall fun z => ((hf z).contDiffAt (hU.mem_nhds hx)).continuousAt)
    exact hc.continuousWithinAt
  | succ N ih =>
    let g : E → α → E →L[ℝ] F := fun x z => fderiv ℝ (fun y => f y z) x
    have hg (z : α) : ContDiffOn ℝ N (fun x => g x z) U :=
      (hf z).fderiv_of_isOpen hU (by norm_cast)
    have hgm (j : ℕ) (hj : j ≤ N) (x : E) (hx : x ∈ U) : AEStronglyMeasurable
        (fun z => iteratedFDeriv ℝ j (fun y => g y z) x) μ := by
      have hh := (continuousMultilinearCurryRightEquiv' ℝ j E F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) (by omega) x hx)
      simpa only [g, iteratedFDeriv_fderiv_eq_curry] using hh
    have hgb (x : E) (hx : x ∈ U) : ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ B : ℕ → α → ℝ,
        (∀ j, j ≤ N → Integrable (B j) μ) ∧
        ∀ j, j ≤ N → ∀ y ∈ s, ∀ z, ‖iteratedFDeriv ℝ j (fun u => g u z) y‖ ≤ B j z := by
      obtain ⟨s, hs, hsu, B, hBi, hB⟩ := hbound x hx
      refine ⟨s, hs, hsu, fun j => B (j+1), fun j hj => hBi _ (by omega), ?_⟩
      intro j hj y hy z
      simpa only [g, norm_iteratedFDeriv_fderiv] using hB (j+1) (by omega) y hy z
    have hD (x : E) (hx : x ∈ U) : HasFDerivAt (fun y => ∫ z, f y z ∂μ)
        (∫ z, g x z ∂μ) x := by
      obtain ⟨s, hs, hsu, B, hBi, hB⟩ := hbound x hx
      have hm (y : E) (hy : y ∈ U) : AEStronglyMeasurable (f y) μ := by
        have hh := (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable
          (hmeas 0 (by omega) y hy)
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using hh
      have hi : Integrable (f x) μ := (hBi 0 (by omega)).mono' (hm x hx)
        (.of_forall fun z => by
          simpa only [norm_iteratedFDeriv_zero] using hB 0 (by omega) x (mem_of_mem_nhds hs) z)
      have hgm0 : AEStronglyMeasurable (g x) μ := by
        have hh := (continuousMultilinearCurryFin0 ℝ E (E →L[ℝ] F)).continuous.comp_aestronglyMeasurable
          (hgm 0 (Nat.zero_le _) x hx)
        simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply] using hh
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
        (Filter.Eventually.mono hs fun y hy => hm y (hsu hy)) hi hgm0 (bound := B 1)
      · exact .of_forall fun z y hy => by
          simpa only [g, norm_iteratedFDeriv_one] using hB 1 (by omega) y hy z
      · exact hBi 1 (by omega)
      · exact .of_forall fun z y hy =>
          (((hf z).contDiffAt (hU.mem_nhds (hsu hy))).differentiableAt (by norm_num)).hasFDerivAt
    apply (contDiffOn_succ_iff_fderiv_of_isOpen (n := (N:ℕ∞ω)) hU).mpr
    refine ⟨fun x hx => (hD x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · simp
    · apply (ih g hg hgm hgb).congr
      intro x hx
      exact (hD x hx).fderiv

end QuantitativePaper
