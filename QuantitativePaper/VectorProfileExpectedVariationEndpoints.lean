module
public import QuantitativePaper.VectorProfileExpectedNodeMatching
public import QuantitativePaper.VectorProfileOuterFunctional
public import QuantitativePaper.VectorMagnetizationGauge

@[expose] public section

/-! Literal actual expected second-variation endpoint values and their
outer-disorder law, including zero overlap and zero terminal variance. -/
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n k : ℕ}

theorem vectorProfileRetainedSecondVariation_initial
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (θ : ℝ)
    (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) :
    vectorProfileRetainedSecondVariation s₀ s₁ β t 0 0 ((θ,p),(0 : Field n))=
      -vectorProfileOuterDerivative s₀ s₁ β t 2 θ p/β := by
  have hq : (0:ℝ)∈Icc (s₀.q 0) (s₀.q 1):=by
    rw [s₀.q_zero]
    exact ⟨le_rfl,s₀.q_nonneg (by omega)⟩
  rw [vectorProfileRetainedSecondVariation_eq_field_closed s₀ s₁ β t ht 0 (by omega) 0 hq _ hθ]
  unfold vectorProfileCellFieldSecondVariation
  rw [vectorProfileCellJointGradient_eq_scheme s₀ s₁ β t 0 (by omega) (0,θ,p) hq
    ⟨hθ.1.le,hθ.2.le⟩ 0,vectorMagnetization_zero_field,
    vectorProfileCellSecondVariation_initial_zero s₀ s₁ β t ht 0 θ hθ p]
  simp only [vectorProfileOuterDerivative,iteratedDeriv_succ,iteratedDeriv_zero]

theorem vectorProfileRetainedSecondVariation_terminal
    (s₀ s₁ : RSBScheme k) (β t : ℝ) (ht : t≤1) (θ : ℝ)
    (hθ : θ∈Ioo (0:ℝ) 1) (p : Couplings n×ℝ) (x : Field n) :
    vectorProfileRetainedSecondVariation s₀ s₁ β t (k+1) 1 ((θ,p),x)=0 := by
  have hq : (1:ℝ)∈Icc (s₀.q (k+1)) (s₀.q (k+2)):=by
    rw [s₀.q_top]
    exact ⟨s₀.q_le_one (by omega),le_rfl⟩
  rw [vectorProfileRetainedSecondVariation_eq_field_closed s₀ s₁ β t ht (k+1) (by omega) 1 hq _ hθ]
  unfold vectorProfileCellFieldSecondVariation
  exact vectorProfileCellSecondVariation_terminal s₀ s₁ β t (k+1) θ hθ p _
    (vectorProfileCellGradient_mem_openSpinCube s₀ s₁ β t (k+1) (by omega) (1,θ,p) hq
      ⟨hθ.1.le,hθ.2.le⟩ x)

theorem vectorProfile_retained_second_variation_expected_terminal
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t (k+1)) 1=0 := by
  unfold vectorProfileRetainedExpectation
  simp only [vectorProfileRetainedSecondVariation_terminal s₀ s₁ β t ht θ hθ,integral_zero]

theorem vectorProfile_retained_second_variation_expected_initial
    (s₀ s₁ : RSBScheme k) (β t outer θ : ℝ) (ht : t≤1)
    (hθ : θ∈Ioo (0:ℝ) 1) :
    vectorProfileRetainedExpectation s₀ s₁ β t outer θ ht ⟨hθ.1.le,hθ.2.le⟩
      (vectorProfileRetainedSecondVariation (n:=n) s₀ s₁ β t 0) 0=
      -(∫p : Couplings n×ℝ,vectorProfileOuterDerivative s₀ s₁ β t 2 θ p
        ∂vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer)/β := by
  unfold vectorProfileRetainedExpectation
  simp only [Real.toNNReal_zero,vectorFiniteState_zero,
    vectorProfileRetainedSecondVariation_initial s₀ s₁ β t ht θ hθ]
  rw [vectorFiniteDisorderTilt_eq_prod]
  have hi : Integrable (vectorProfileOuterDerivative (n:=n) s₀ s₁ β t 2 θ)
      (vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer):=by
    simpa only [pow_one] using integrable_vectorProfileOuterDerivative_pow s₀ s₁ β t ht outer 2 1 θ hθ
  letI:=vectorOuterLaw_probability (n:=n) (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer
  have he:=integral_fun_fst
    (μ:=vectorOuterLaw (vectorProfileScheme s₀ s₁ θ ⟨hθ.1.le,hθ.2.le⟩) β t outer)
    (ν:=vectorBrownianMeasure n) (fun p : Couplings n×ℝ=> -vectorProfileOuterDerivative s₀ s₁ β t 2 θ p/β)
  rw [show (vectorBrownianMeasure n).real univ=1 by simp [Measure.real],one_smul] at he
  exact he.trans (by rw [integral_div,integral_neg])

end QuantitativePaper
