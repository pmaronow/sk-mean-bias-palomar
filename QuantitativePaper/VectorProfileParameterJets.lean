module
public import QuantitativePaper.VectorProfileGrowth
public import QuantitativePaper.ScalarCylinderJets
public import QuantitativePaper.BoundedPositiveJets

@[expose] public section

/-! Actual affine masses, their selected positive inverse branch, and the
terminal profile function have the parameter jets used in profile smoothing. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000

def vectorProfileJointFunction {n k : ℕ} (s₀ s₁ : RSBScheme k) (β t : ℝ)
    (j : ℕ) (z : ℝ×VectorParameter n) : ℝ :=
  vectorProfileRecursion s₀ s₁ β t z.1 z.2.1 j z.2.2

def vectorProfileJointShift (n : ℕ) (c : ℝ) : Field n →L[ℝ] (ℝ×VectorParameter n) :=
  (0 : Field n →L[ℝ] ℝ).prod (vectorJointShift n c)

theorem vectorProfileJointShift_add (n : ℕ) (c : ℝ)
    (x : ℝ×VectorParameter n) (z : Field n) :
    x+vectorProfileJointShift n c z = (x.1, x.2.1, fieldShift c x.2.2 z) := by
  ext
  · simp [vectorProfileJointShift]
  · simp [vectorProfileJointShift, vectorJointShift]
  · simp [vectorProfileJointShift, vectorJointShift]
  · rfl

theorem contDiff_vectorProfileMass {k : ℕ} (s₀ s₁ : RSBScheme k) (i : ℕ) (N : ℕ) :
    ContDiff ℝ N (fun θ => vectorProfileMass s₀ s₁ θ i) := by
  unfold vectorProfileMass
  fun_prop

theorem vectorProfileMass_mem_unit {k : ℕ} (s₀ s₁ : RSBScheme k)
    (i : ℕ) (hi : i ≤ k+1) (θ : ℝ) (hθ : θ ∈ Icc (0:ℝ) 1) :
    vectorProfileMass s₀ s₁ θ i ∈ Icc (0:ℝ) 1 := by
  let s := vectorProfileScheme s₀ s₁ θ hθ
  exact ⟨s.m_nonneg hi, s.m_le_one hi⟩

theorem exists_vectorProfileMass_cylinder_bound {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (i N : ℕ) (a b : ℝ) : ∃ M : ℝ, 1 ≤ M ∧ ∀ j, j ≤ N →
      ∀ z : ℝ×VectorParameter n, z.1 ∈ Icc a b →
      ‖iteratedFDeriv ℝ j (fun z : ℝ×VectorParameter n => vectorProfileMass s₀ s₁ z.1 i) z‖ ≤ M :=
  exists_scalar_cylinder_jet_bound N _ univ isOpen_univ
    (contDiff_vectorProfileMass s₀ s₁ i N).contDiffOn a b (subset_univ _)

theorem exists_vectorProfileMass_inverse_cylinder_bound {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (i N : ℕ) (hpos : ∀ θ ∈ Ioo (0:ℝ) 1, 0 < vectorProfileMass s₀ s₁ θ i)
    (a b : ℝ) (ha : 0 < a) (hb : b < 1) : ∃ M : ℝ, 1 ≤ M ∧ ∀ j, j ≤ N →
      ∀ z : ℝ×VectorParameter n, z.1 ∈ Icc a b →
      ‖iteratedFDeriv ℝ j (fun z : ℝ×VectorParameter n => (vectorProfileMass s₀ s₁ z.1 i)⁻¹) z‖ ≤ M := by
  have hf : ContDiffOn ℝ N (fun θ => (vectorProfileMass s₀ s₁ θ i)⁻¹) (Ioo (0:ℝ) 1) :=
    (contDiff_vectorProfileMass s₀ s₁ i N).contDiffOn.inv (fun θ hθ => (hpos θ hθ).ne')
  exact exists_scalar_cylinder_jet_bound N _ _ isOpen_Ioo hf a b
    (fun θ hθ => ⟨ha.trans_le hθ.1, hθ.2.trans_lt hb⟩)

theorem vectorProfileJointFunction_linear_growth {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (j : ℕ) :
    ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ ∀ z : ℝ×VectorParameter n,
      z.1 ∈ Icc (0:ℝ) 1 → |vectorProfileJointFunction s₀ s₁ β t j z| ≤ B+L*‖z‖ := by
  let B := |vectorTerminalPotential n β t (0 : Couplings n×ℝ) (0 : Field n)|+
    (j:ℝ)*(n:ℝ)/2*((1-t)*β^2)
  let L := (vectorJointLipschitzConstant n β t:ℝ)
  refine ⟨B, L, by dsimp only [B]; positivity, (vectorJointLipschitzConstant n β t).coe_nonneg, ?_⟩
  intro z hθ
  exact (vectorProfileRecursion_abs_le s₀ s₁ β t ht z.1 hθ j z.2).trans
    (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left (norm_snd_le z) (by positivity)))

theorem boundedPositiveJets_power_bound {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hf : BoundedPositiveJets f) (N : ℕ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ j, 1 ≤ j → j ≤ N → ∀ x,
      ‖iteratedFDeriv ℝ j f x‖ ≤ K^j := by
  classical
  let B : ℕ → ℝ := fun j => if hj : 1 ≤ j then Classical.choose (hf.2 j hj) else 0
  refine ⟨finiteJetPowerBound B N, finiteJetPowerBound_ge_one B N, ?_⟩
  intro j hj0 hj x
  have hh : ‖iteratedFDeriv ℝ j f x‖ ≤ B j := by
    dsimp only [B]
    rw [dif_pos hj0]
    exact (Classical.choose_spec (hf.2 j hj0)).2 x
  exact hh.trans (finite_jet_bound_le_power B N j hj0 hj)

end QuantitativePaper
