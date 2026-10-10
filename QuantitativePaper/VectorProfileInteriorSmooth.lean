module
public import QuantitativePaper.VectorProfileSmooth

@[expose] public section

/-! The actual affine-profile recursion is jointly smooth in the interior
profile parameter, all disorder coordinates and all field coordinates.
The restarted recursion is the same physical construction on the clamped
scheme, with its dummy root interval omitted. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ContDiff NNReal
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1800000

theorem contDiffAt_vectorProfileJointFunction {n k : ℕ} (s₀ s₁ : RSBScheme k)
    (β t : ℝ) (ht : t ≤ 1) (j : ℕ) (x : ℝ×VectorParameter n)
    (hx : x.1 ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞ (vectorProfileJointFunction s₀ s₁ β t j) x := by
  apply contDiffAt_infty.mpr
  intro N
  have h := (vectorProfileJointFunction_smooth_exp_jets_on_cylinder (n:=n) s₀ s₁ β t ht N j
    (x.1/2) ((x.1+1)/2) (by linarith [hx.1]) (by linarith [hx.2])).1
  have hmem : x ∈ {z : ℝ×VectorParameter n | z.1 ∈ Ioo (x.1/2) ((x.1+1)/2)} := by
    constructor <;> linarith [hx.1,hx.2]
  exact (h x hmem).contDiffAt ((isOpen_Ioo.preimage continuous_fst).mem_nhds hmem)

theorem vectorProfileTailRecursion_eq_clampedProfile {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t q θ : ℝ) (hq : q ∈ Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) {j : ℕ} (hj : j ≤ k+2) :
    vectorProfileTailRecursion s₀ s₁ β t q θ p j =
      vectorProfileRecursion (vectorClampedScheme s₀ q hq) (vectorClampedScheme s₁ q hq)
        β t θ p j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [vectorProfileTailRecursion, vectorProfileRecursion, ih (by omega)]
    have hi : k+1+1-j=(k+1-j)+1 := by omega
    have hi' : k+1+2-j=(k+2-j)+1 := by omega
    rw [hi,hi']
    simp only [vectorProfileMass, vectorClampedScheme_mass_succ,
      vectorClampedScheme_overlap_succ]
    simp only [show k+1-j+1=k+2-j by omega]

theorem contDiffAt_vectorProfileTailRecursion_joint {n k : ℕ}
    (s₀ s₁ : RSBScheme k) (β t q : ℝ) (ht : t ≤ 1) (hq : q ∈ Icc (0:ℝ) 1)
    (j : ℕ) (hj : j ≤ k+2) (x : ℝ×VectorParameter n) (hx : x.1 ∈ Ioo (0:ℝ) 1) :
    ContDiffAt ℝ ∞
      (fun z : ℝ×VectorParameter n => vectorProfileTailRecursion s₀ s₁ β t q z.1 z.2.1 j z.2.2) x := by
  have he : (fun z : ℝ×VectorParameter n => vectorProfileTailRecursion s₀ s₁ β t q z.1 z.2.1 j z.2.2) =
      vectorProfileJointFunction (vectorClampedScheme s₀ q hq) (vectorClampedScheme s₁ q hq) β t j := by
    funext z
    exact congrFun (vectorProfileTailRecursion_eq_clampedProfile s₀ s₁ β t q z.1 hq z.2.1 hj) z.2.2
  rw [he]
  exact contDiffAt_vectorProfileJointFunction _ _ β t ht j x hx

end QuantitativePaper
