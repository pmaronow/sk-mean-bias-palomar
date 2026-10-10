module
public import QuantitativePaper.VectorGridProfileClosedJetBounds
public import QuantitativePaper.VectorProfileOuterMoments

@[expose] public section

/-! The literal disorder-dependent initial potential derivatives inherit
the actual depth-independent restarted profile bounds. -/
noncomputable section
open Set Filter
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 1700000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorGridProfile_initial_eventually_eq_tail
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (p : Couplings n×ℝ)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    (fun φ=>vectorProfileRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t φ p (vectorDyadicIndex j+3) 0)=ᶠ[𝓝 θ]
    (vectorGridProfileTailFunction μ ν β t ⟨0,by norm_num⟩ p 0 j) := by
  filter_upwards [isOpen_Ioo.mem_nhds hθ] with φ hφ
  unfold vectorGridProfileTailFunction
  rw [vectorProfileTailRecursion_eq_scheme _ _ β t 0 φ ⟨hφ.1.le,hφ.2.le⟩,
    vectorTailRecursion_zero _ β t p le_rfl,
    vectorProfileRecursion_eq_scheme _ _ β t φ ⟨hφ.1.le,hφ.2.le⟩]

theorem abs_vectorGridProfileOuterDerivative_one_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (ht : t≤1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) :
    |vectorProfileOuterDerivative (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t 1 θ p|≤(n:ℝ)*((1-t)*β^2)/2 := by
  have he:=vectorGridProfile_initial_eventually_eq_tail μ ν j β t p θ hθ
  unfold vectorProfileOuterDerivative
  rw [he.iteratedDeriv_eq 1,iteratedDeriv_one,←Real.norm_eq_abs]
  change ‖deriv (fun φ=>vectorProfileTailRecursion
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
    (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t 0 φ p (vectorDyadicIndex j+3) 0) θ‖≤_
  simpa only [sub_zero,mul_one] using
    norm_vectorProfileTailRecursion_profile_deriv_le
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) (fun _ _=>rfl) β t 0 θ ht
        (by norm_num) hθ p (0:Field n)

theorem abs_vectorGridProfileOuterDerivative_two_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) :
    |vectorProfileOuterDerivative (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t 2 θ p|≤vectorProfileSecondReactionBound n β t := by
  have he:=vectorGridProfile_initial_eventually_eq_tail μ ν j β t p θ hθ
  unfold vectorProfileOuterDerivative
  rw [he.iteratedDeriv_eq 2]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Real.norm_eq_abs] using
    norm_vectorGridProfileTailFunction_second_deriv_closed_le μ ν j β t hβ ht
      ⟨0,by norm_num⟩ p (0:Field n) θ ⟨hθ.1.le,hθ.2.le⟩

theorem abs_vectorGridProfileOuterDerivative_three_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) :
    |vectorProfileOuterDerivative (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t 3 θ p|≤vectorProfileThirdReactionBound n β t := by
  have he:=vectorGridProfile_initial_eventually_eq_tail μ ν j β t p θ hθ
  unfold vectorProfileOuterDerivative
  rw [he.iteratedDeriv_eq 3]
  simpa only [iteratedDeriv_succ,iteratedDeriv_zero,Real.norm_eq_abs] using
    norm_vectorGridProfileTailFunction_third_deriv_closed_le μ ν j β t hβ ht
      ⟨0,by norm_num⟩ p (0:Field n) θ ⟨hθ.1.le,hθ.2.le⟩

end QuantitativePaper
