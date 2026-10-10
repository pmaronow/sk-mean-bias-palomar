module
public import QuantitativePaper.LocalSmoothIntegral

@[expose] public section

/-! Actual higher derivatives of a parameter integral on an open domain. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {α : Type} [MeasurableSpace α]
set_option maxHeartbeats 1400000

set_option backward.isDefEq.respectTransparency false in
theorem iteratedFDeriv_integral_of_locally_dominated_derivatives {F : Type}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (N : ℕ) (μ : Measure α) (f : E → α → F) (U : Set E) (hU : IsOpen U)
    (hf : ∀ z, ContDiffOn ℝ N (fun x => f x z) U)
    (hmeas : ∀ j, j ≤ N → ∀ x ∈ U, AEStronglyMeasurable
      (fun z => iteratedFDeriv ℝ j (fun y => f y z) x) μ)
    (hbound : ∀ x ∈ U, ∃ s ∈ 𝓝 x, s ⊆ U ∧ ∃ B : ℕ → α → ℝ,
      (∀ j, j ≤ N → Integrable (B j) μ) ∧
      ∀ j, j ≤ N → ∀ y ∈ s, ∀ z, ‖iteratedFDeriv ℝ j (fun u => f u z) y‖ ≤ B j z)
    (j : ℕ) (hj : j ≤ N) (x : E) (hx : x ∈ U) :
    iteratedFDeriv ℝ j (fun y => ∫ z, f y z ∂μ) x =
      ∫ z, iteratedFDeriv ℝ j (fun y => f y z) x ∂μ := by
  induction j generalizing x with
  | zero =>
    simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
    exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm _).symm
  | succ j ih =>
    let F₀ := fun y z => iteratedFDeriv ℝ j (fun u => f u z) y
    let F₁ := fun y z => fderiv ℝ (fun u => F₀ u z) y
    have he : iteratedFDeriv ℝ j (fun y => ∫ z, f y z ∂μ) =ᶠ[𝓝 x]
        fun y => ∫ z, F₀ y z ∂μ := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih (by omega) y hy
    obtain ⟨s, hs, hsu, B, hBi, hB⟩ := hbound x hx
    have hF₀ (y : E) (hy : y ∈ U) : AEStronglyMeasurable (F₀ y) μ :=
      hmeas j (by omega) y hy
    have hF₁ : AEStronglyMeasurable (F₁ x) μ := by
      have hh := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j+1) => E) F).continuous.comp_aestronglyMeasurable
        (hmeas (j+1) hj x hx)
      simpa only [F₀, F₁, fderiv_iteratedFDeriv, Function.comp_apply] using hh
    have hi : Integrable (F₀ x) μ := (hBi j (by omega)).mono' (hF₀ x hx)
      (.of_forall fun z => hB j (by omega) x (mem_of_mem_nhds hs) z)
    have hd : HasFDerivAt (fun y => ∫ z, F₀ y z ∂μ) (∫ z, F₁ x z ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le hs
        (Filter.Eventually.mono hs fun y hy => hF₀ y (hsu hy)) hi hF₁
        (bound := B (j+1))
      · exact .of_forall fun z y hy => by
          simpa only [F₀, F₁, norm_fderiv_iteratedFDeriv] using hB (j+1) hj y hy z
      · exact hBi (j+1) hj
      · exact .of_forall fun z y hy =>
          (((hf z).contDiffAt (hU.mem_nhds (hsu hy))).differentiableAt_iteratedFDeriv
            (by norm_cast)).hasFDerivAt
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, he.fderiv_eq, hd.fderiv]
    have hi₁ := integrable_clm_of_norm_bound μ (F₁ x) (B (j+1)) (hBi (j+1) hj) hF₁
      (fun z => by
        simpa only [F₀, F₁, norm_fderiv_iteratedFDeriv]
          using hB (j+1) hj x (mem_of_mem_nhds hs) z)
    have hij : Integrable (fun z => iteratedFDeriv ℝ (j+1) (fun y => f y z) x) μ :=
      (hBi (j+1) hj).mono' (hmeas (j+1) hj x hx)
        (.of_forall fun z => hB (j+1) hj x (mem_of_mem_nhds hs) z)
    ext v
    change (∫ z, F₁ x z ∂μ) (v 0) (Fin.tail v) = _
    rw [ContinuousLinearMap.integral_apply hi₁, ContinuousMultilinearMap.integral_apply hij]
    rw [ContinuousMultilinearMap.integral_apply (hi₁.apply_continuousLinearMap (v 0))]
    apply integral_congr_ae
    exact .of_forall fun z => by
      simp only [F₀, F₁, iteratedFDeriv_succ_apply_left]

end QuantitativePaper
