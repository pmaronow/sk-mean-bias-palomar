module
public import QuantitativePaper.VectorProfileUniformFirstVariation
public import QuantitativePaper.VectorNodeGradient

@[expose] public section

/-! The actual first profile derivative at every finite backward depth has
the same dimension-only bound. Node identification keeps repeated nodes and
the terminal node; no strictly increasing mesh is required. -/
noncomputable section
open Set Filter
open scoped Topology NNReal ContDiff
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1300000

theorem vectorProfileRecursion_at_node_eq_tail {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (j : ℕ) (hj : j ≤ k+2) :
    vectorProfileRecursion s₀ s₁ β t θ p j =
      vectorProfileTailRecursion s₀ s₁ β t (s₀.q (k+2-j)) θ p (k+2) := by
  rw [vectorProfileRecursion_eq_scheme s₀ s₁ β t θ hθ,
    vectorProfileTailRecursion_eq_scheme s₀ s₁ β t _ θ hθ]
  have hi : k+2-j ≤ k+2 := Nat.sub_le _ _
  have hnode : s₀.q (k+2-j)=(vectorProfileScheme s₀ s₁ θ hθ).q (k+2-j) := rfl
  rw [hnode,vectorTailRecursion_at_node _ β t _ hi p,
    show k+2-(k+2-j)=j by omega]

theorem vectorProfileRecursion_lipschitzOn_profile {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t : ℝ) (ht : t ≤ 1) (p : Couplings n×ℝ)
    (j : ℕ) (hj : j ≤ k+2) (x : Field n) :
    LipschitzOnWith ((n:ℝ)*((1-t)*β^2)/2*(1-s₀.q (k+2-j))).toNNReal
      (fun θ => vectorProfileRecursion s₀ s₁ β t θ p j x) (Icc (0:ℝ) 1) := by
  have hq : s₀.q (k+2-j) ∈ Icc (0:ℝ) 1 :=
    ⟨s₀.q_nonneg (Nat.sub_le _ _),s₀.q_le_one (Nat.sub_le _ _)⟩
  have hh := vectorProfileTailRecursion_lipschitzOn_profile s₀ s₁ hgrid β t
    (s₀.q (k+2-j)) ht hq p x
  rw [lipschitzOnWith_iff_dist_le_mul] at hh ⊢
  intro θ hθ φ hφ
  rw [vectorProfileRecursion_at_node_eq_tail s₀ s₁ β t θ hθ p j hj,
    vectorProfileRecursion_at_node_eq_tail s₀ s₁ β t φ hφ p j hj]
  exact hh θ hθ φ hφ

theorem norm_vectorProfileRecursion_profile_deriv_le {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (hgrid : ∀ i, i ≤ k+2 → s₀.q i=s₁.q i)
    (β t θ : ℝ) (ht : t ≤ 1) (hθ : θ ∈ Ioo (0:ℝ) 1)
    (p : Couplings n×ℝ) (j : ℕ) (hj : j ≤ k+2) (x : Field n) :
    ‖deriv (fun φ => vectorProfileRecursion s₀ s₁ β t φ p j x) θ‖ ≤
      (n:ℝ)*((1-t)*β^2)/2 := by
  have hn : 0 ≤ (n:ℝ)*((1-t)*β^2)/2 := by positivity
  have hq := s₀.q_nonneg (Nat.sub_le (k+2) j)
  have hq1 := s₀.q_le_one (Nat.sub_le (k+2) j)
  have hh := norm_deriv_le_of_lipschitzOn (Icc_mem_nhds hθ.1 hθ.2)
    (vectorProfileRecursion_lipschitzOn_profile s₀ s₁ hgrid β t ht p j hj x)
  rw [Real.coe_toNNReal _ (mul_nonneg hn (sub_nonneg.mpr hq1))] at hh
  exact hh.trans (by nlinarith)

theorem vectorProfileRecursion_hasDerivAt_profile {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t θ : ℝ) (ht : t ≤ 1)
    (hθ : θ ∈ Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (j : ℕ) (x : Field n) :
    HasDerivAt (fun φ => vectorProfileRecursion s₀ s₁ β t φ p j x)
      (deriv (fun φ => vectorProfileRecursion s₀ s₁ β t φ p j x) θ) θ := by
  have hs := contDiffAt_vectorProfileJointFunction s₀ s₁ β t ht j (θ,(p,x)) hθ
  have hc : ContDiffAt ℝ ∞ (fun φ : ℝ => (φ,(p,x))) θ :=
    contDiffAt_id.prodMk contDiffAt_const
  exact ((hs.comp θ hc).differentiableAt (by simp)).hasDerivAt

end QuantitativePaper
