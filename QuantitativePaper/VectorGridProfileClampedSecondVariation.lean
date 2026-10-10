module
public import QuantitativePaper.VectorGridProfileUniformSecondVariation
public import QuantitativePaper.VectorProfilePosteriorSecondScore

@[expose] public section

/-! Every remaining clamped posterior node inherits the actual uniform
second profile derivative bound; no posterior second-jet bound is assumed. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorTailRecursion_clamped_prefix_eq_tail (s : RSBScheme k)
    (β t q : ℝ) (p : Couplings n×ℝ) (J : ℕ) (hJ : J≤k+2) :
    vectorTailRecursion s β t q p J=
      vectorTailRecursion s β t (max q (s.q (k+2-J))) p (k+2) := by
  by_cases hq : q ≤ s.q (k+2-J)
  · rw [max_eq_right hq,vectorTailRecursion_prefix_of_le s β t q p hJ hq,
      vectorTailRecursion_at_node s β t (k+2-J) (by omega) p]
    rw [show k+2-(k+2-J)=J by omega]
  · rw [max_eq_left (le_of_not_ge hq)]
    exact (vectorTailRecursion_constant_suffix s β t q p J hJ (le_of_not_ge hq) hJ le_rfl).symm

theorem vectorProfileClampedRecursion_eq_tail (s₀ s₁ : RSBScheme k)
    (β t q θ : ℝ) (hq : q∈Icc (0:ℝ) 1) (hθ : θ∈Icc (0:ℝ) 1)
    (p : Couplings n×ℝ) (J : ℕ) (hJ : J≤k+2) :
    vectorProfileRecursion (vectorClampedScheme s₀ q hq) (vectorClampedScheme s₁ q hq)
      β t θ p J=
    vectorProfileTailRecursion s₀ s₁ β t (max q (s₀.q (k+2-J))) θ p (k+2) := by
  rw [vectorProfileRecursion_eq_scheme _ _ β t θ hθ,
    vectorProfileScheme_clamped s₀ s₁ q θ hq hθ,
    ←vectorTailRecursion_eq_clamped _ β t q hq p hJ,
    vectorTailRecursion_clamped_prefix_eq_tail _ β t q p J hJ,
    vectorProfileTailRecursion_eq_scheme s₀ s₁ β t _ θ hθ]
  rfl

theorem norm_vectorGridProfileClampedRecursion_second_profile_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (q : Paper.Overlap) (p : Couplings n×ℝ) (x : Field n)
    (J : ℕ) (hJ : J≤vectorDyadicIndex j+3) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    ‖deriv (deriv (fun φ=>vectorProfileRecursion
      (vectorClampedScheme (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) q q.property)
      (vectorClampedScheme (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) q q.property)
      β t φ p J x)) θ‖≤vectorProfileSecondReactionBound n β t := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  let r:=max (q:ℝ) (s₀.q (vectorDyadicIndex j+3-J))
  have hr : r∈Icc (0:ℝ) 1:=⟨q.property.1.trans (le_max_left _ _),
    max_le q.property.2 (s₀.q_le_one (by omega))⟩
  have he : (fun φ=>vectorProfileRecursion (vectorClampedScheme s₀ q q.property)
      (vectorClampedScheme s₁ q q.property) β t φ p J x)=ᶠ[𝓝 θ]
      (fun φ=>vectorProfileTailRecursion s₀ s₁ β t r φ p (vectorDyadicIndex j+3) x) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
    exact congrFun (vectorProfileClampedRecursion_eq_tail s₀ s₁ β t q φ q.property
      ⟨hφ.1.le,hφ.2.le⟩ p J hJ) x
  rw [he.deriv.deriv_eq]
  exact norm_vectorGridProfileTailRecursion_second_profile_deriv_le μ ν j β t hβ ht ⟨r,hr⟩ p x θ hθ

end QuantitativePaper
