module
public import QuantitativePaper.VectorGridProfileOuterPartitionJetBounds
public import QuantitativePaper.ScalarPartitionThirdBound
public import QuantitativePaper.VectorProfileEndpointOuterRegularity

@[expose] public section

/-! Depth-independent jets of the literal fractional outer log-partition.
The zero-tilt branch is differentiated as its actual Gaussian mean. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology ContDiff
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon
set_option maxHeartbeats 300000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorProfileOuterSecondJetBound (n : ℕ) (β t outer : ℝ) : ℝ:=
  vectorProfileSecondReactionBound n β t+2*|outer| *((n:ℝ)*((1-t)*β^2)/2)^2

def vectorProfileOuterThirdJetBound (n : ℕ) (β t outer : ℝ) : ℝ:=
  vectorProfileThirdReactionBound n β t+
    6*|outer| *((n:ℝ)*((1-t)*β^2)/2)*vectorProfileSecondReactionBound n β t+
      6*outer^2*((n:ℝ)*((1-t)*β^2)/2)^3

theorem vectorProfileOuterSecondJetBound_nonneg (n : ℕ) (β t outer : ℝ) (ht : t≤1) :
    0≤vectorProfileOuterSecondJetBound n β t outer:=by
  unfold vectorProfileOuterSecondJetBound
  exact add_nonneg (vectorProfileSecondReactionBound_nonneg n β t ht) (by positivity)

theorem vectorProfileOuterThirdJetBound_nonneg (n : ℕ) (β t outer : ℝ) (ht : t≤1) :
    0≤vectorProfileOuterThirdJetBound n β t outer:=by
  unfold vectorProfileOuterThirdJetBound
  have hm:=vectorProfileSecondReactionBound_nonneg n β t ht
  have hr:=vectorProfileThirdReactionBound_nonneg n β t ht
  have hc : 0≤1-t:=sub_nonneg.mpr ht
  positivity

private theorem norm_zero_outer_jet_le (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ)
    (ht : t≤1) (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) (r : ℕ) (C : ℝ)
    (hb : ∀p : Couplings n×ℝ,|vectorProfileOuterDerivative
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t r θ p|≤C) :
    |iteratedDeriv r (vectorProfileOuterNormalized (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t 0) θ|≤C := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t 0=
      (fun y=>∫p : Couplings n×ℝ,vectorProfileRecursion s₀ s₁ β t y p
        (vectorDyadicIndex j+3) 0 ∂completionLaw n):=
    funext fun y=>vectorProfileOuterNormalized_zero_all_theta s₀ s₁ β t y
  rw [he]
  have hdiff:=(vectorProfileOuter_dominatedJets_all_theta (n:=n) s₀ s₁ β t r
    (vectorDyadicIndex j+3) (θ-1) (θ+1)).iteratedDeriv_integral
      isOpen_Ioo le_rfl (by constructor <;>linarith : θ∈Ioo (θ-1) (θ+1))
  rw [hdiff,←Real.norm_eq_abs]
  simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
    (μ:=completionLaw n) (.of_forall fun p=>by
      simpa only [Real.norm_eq_abs,vectorProfileOuterDerivative,s₀,s₁] using hb p)

theorem abs_vectorGridProfileOuterNormalized_second_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    |iteratedDeriv 2 (vectorProfileOuterNormalized (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t outer) θ|≤
        vectorProfileOuterSecondJetBound n β t outer := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  by_cases ho : outer=0
  · subst outer
    simpa only [vectorProfileOuterSecondJetBound,abs_zero,mul_zero,zero_mul,add_zero] using
      norm_zero_outer_jet_le μ ν j β t ht.le θ hθ 2 _
        (fun p=>abs_vectorGridProfileOuterDerivative_two_le μ ν j β t hβ ht θ hθ p)
  · have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
        fun y=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y)/outer:=
      funext fun y=>vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer y ho
    rw [he]
    apply abs_normalized_log_second_deriv_le _ (Ioo (0:ℝ) 1) isOpen_Ioo
      ((contDiff_vectorProfileOuterPartition_all_theta s₀ s₁ β t outer).contDiffOn.of_le (by simp))
      (fun y _=>vectorProfileOuterPartition_pos_all_theta s₀ s₁ β t outer y)
      outer ((n:ℝ)*((1-t)*β^2)/2) (vectorProfileSecondReactionBound n β t)
      ho (by positivity) (vectorProfileSecondReactionBound_nonneg n β t ht.le) hθ
    · simpa only [iteratedDeriv_one,Real.norm_eq_abs,scalarExponentialJetBound] using
        norm_vectorGridProfileOuterPartition_jet_le μ ν j β t hβ ht outer θ hθ 1 (by decide)
    · simpa only [Real.norm_eq_abs,scalarExponentialJetBound] using
        norm_vectorGridProfileOuterPartition_jet_le μ ν j β t hβ ht outer θ hθ 2 (by decide)

theorem abs_vectorGridProfileOuterNormalized_third_deriv_le
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t : ℝ) (hβ : β≠0) (ht : t<1)
    (outer θ : ℝ) (hθ : θ∈Ioo (0:ℝ) 1) :
    |iteratedDeriv 3 (vectorProfileOuterNormalized (n:=n)
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t outer) θ|≤
        vectorProfileOuterThirdJetBound n β t outer := by
  let s₀:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let s₁:=Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)
  by_cases ho : outer=0
  · subst outer
    simpa only [vectorProfileOuterThirdJetBound,abs_zero,zero_pow (by decide : 2≠0),
      mul_zero,zero_mul,add_zero] using
      norm_zero_outer_jet_le μ ν j β t ht.le θ hθ 3 _
        (fun p=>abs_vectorGridProfileOuterDerivative_three_le μ ν j β t hβ ht θ hθ p)
  · have he : vectorProfileOuterNormalized (n:=n) s₀ s₁ β t outer=
        fun y=>Real.log (vectorProfileOuterPartition (n:=n) s₀ s₁ β t outer y)/outer:=
      funext fun y=>vectorProfileOuterNormalized_of_ne s₀ s₁ β t outer y ho
    rw [he]
    apply abs_normalized_log_third_deriv_le _ (Ioo (0:ℝ) 1) isOpen_Ioo
      ((contDiff_vectorProfileOuterPartition_all_theta s₀ s₁ β t outer).contDiffOn.of_le (by simp))
      (fun y _=>vectorProfileOuterPartition_pos_all_theta s₀ s₁ β t outer y)
      outer ((n:ℝ)*((1-t)*β^2)/2) (vectorProfileSecondReactionBound n β t)
      (vectorProfileThirdReactionBound n β t) ho (by positivity) (vectorProfileSecondReactionBound_nonneg n β t ht.le)
      (vectorProfileThirdReactionBound_nonneg n β t ht.le) hθ
    · simpa only [iteratedDeriv_one,Real.norm_eq_abs,scalarExponentialJetBound] using
        norm_vectorGridProfileOuterPartition_jet_le μ ν j β t hβ ht outer θ hθ 1 (by decide)
    · simpa only [Real.norm_eq_abs,scalarExponentialJetBound] using
        norm_vectorGridProfileOuterPartition_jet_le μ ν j β t hβ ht outer θ hθ 2 (by decide)
    · simpa only [Real.norm_eq_abs,scalarExponentialJetBound] using
        norm_vectorGridProfileOuterPartition_jet_le μ ν j β t hβ ht outer θ hθ 3 (by decide)

end QuantitativePaper
