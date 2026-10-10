module
public import QuantitativePaper.LocalJetBounds
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! Actual bounded scalar-parameter jets pull back to a whole cylinder.
Compactness bounds all selected derivative orders without assuming a bound on
the other parameters or an extension through a singular scalar value. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace QuantitativePaper
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
set_option maxHeartbeats 1400000

theorem exists_scalar_cylinder_jet_bound (N : ℕ) (f : ℝ → ℝ)
    (U : Set ℝ) (hU : IsOpen U) (hf : ContDiffOn ℝ N f U)
    (a b : ℝ) (hsub : Icc a b ⊆ U) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ j, j ≤ N → ∀ x : ℝ×E, x.1 ∈ Icc a b →
      ‖iteratedFDeriv ℝ j (fun y : ℝ×E => f y.1) x‖ ≤ M := by
  classical
  have hbound (j : ℕ) (hj : j ≤ N) : ∃ C : ℝ, ∀ θ ∈ Icc a b,
      ‖iteratedFDeriv ℝ j f θ‖ ≤ C := by
    have hc := (hf.continuousOn_iteratedFDerivWithin (by exact_mod_cast hj) hU.uniqueDiffOn).mono hsub
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
    refine ⟨C, fun θ hθ => ?_⟩
    simpa only [iteratedFDerivWithin_of_isOpen j hU (hsub hθ)] using hC θ hθ
  let C : ℕ → ℝ := fun j => if hj : j ≤ N then Classical.choose (hbound j hj) else 0
  let M : ℝ := max 1 (∑ j ∈ Finset.range (N+1), |C j|)
  refine ⟨M, le_max_left _ _, ?_⟩
  intro j hj x hx
  let A : ℝ×E →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ E
  have hA : ‖A‖ ≤ 1 := ContinuousLinearMap.norm_fst_le ℝ ℝ E
  have hv : IsOpen (A ⁻¹' U) := hU.preimage A.continuous
  have hxU : A x ∈ U := hsub hx
  have he := A.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hv.uniqueDiffOn
    hxU (by exact_mod_cast hj)
  rw [iteratedFDerivWithin_of_isOpen j hv hxU,
    iteratedFDerivWithin_of_isOpen j hU hxU] at he
  change ‖iteratedFDeriv ℝ j (f ∘ A) x‖ ≤ _
  rw [he]
  have hn := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j f (A x)) (fun _ : Fin j => A)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hn
  apply hn.trans
  have hCp : ‖iteratedFDeriv ℝ j f (A x)‖ ≤ C j := by
    dsimp only [C]
    rw [dif_pos hj]
    exact Classical.choose_spec (hbound j hj) x.1 hx
  have hnorm : ‖A‖^j ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg A) hA j
  have hs : C j ≤ M := by
    exact (le_abs_self _).trans ((Finset.single_le_sum (f:=fun j => |C j|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))).trans (le_max_right _ _))
  have hC0 : 0 ≤ C j := (norm_nonneg _).trans hCp
  exact (mul_le_mul hCp hnorm (pow_nonneg (norm_nonneg A) _) hC0).trans (by simpa only [mul_one] using hs)

end QuantitativePaper
