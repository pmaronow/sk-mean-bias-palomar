module
public import QuantitativePaper.VectorUniformVarianceJets
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-! Actual joint disorder/field jet bounds imply literal field jet bounds,
uniform in overlap time. The fixed-disorder insertion has operator norm ≤1. -/
noncomputable section
open scoped ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 400000

theorem vectorFiniteCellPotential_uniform_field_jets {n k : ℕ} (s : RSBScheme k)
    (β t : ℝ) (i N : ℕ) :
    ∃K : ℝ,1 ≤ K ∧ ∀q : ℝ,∀j,1 ≤ j → j ≤ N →
      ∀p : Couplings n×ℝ,∀x : Field n,
      ‖iteratedFDeriv ℝ j (vectorFiniteCellPotential s β t p i q) x‖ ≤ K^j := by
  obtain ⟨K,hK,hB⟩ := vectorFiniteCellPotential_uniform_spatial_jets (n := n) s β t i N
  refine ⟨K,hK,?_⟩
  intro q j hj0 hj p x
  let L : Field n→L[ℝ] VectorParameter n := ContinuousLinearMap.inr ℝ (Couplings n×ℝ) (Field n)
  have hL : ‖L‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    simp [L,Prod.norm_def]
  let F := fun z : VectorParameter n => vectorFiniteCellPotential s β t z.1 i q z.2
  let G := fun z : VectorParameter n => F (z+(p,0))
  have hG : ContDiff ℝ ∞ G := (contDiff_vectorFiniteCellPotential_joint s β t i q).comp
    (contDiff_id.add contDiff_const)
  have he : vectorFiniteCellPotential s β t p i q=G ∘ L := by
    funext y
    simp [G,F,L,Function.comp_def]
  rw [he,L.iteratedFDeriv_comp_right hG x (by simp)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [iteratedFDeriv_comp_add_right]
  have hh := mul_le_mul_of_nonneg_right (hB q j hj0 hj (L x+(p,0))) (pow_nonneg (norm_nonneg L) j)
  apply hh.trans
  have hp : ‖L‖^j ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg L) hL j
  exact (mul_le_mul_of_nonneg_left hp (pow_nonneg (zero_le_one.trans hK) j)).trans_eq (mul_one _)

end QuantitativePaper
