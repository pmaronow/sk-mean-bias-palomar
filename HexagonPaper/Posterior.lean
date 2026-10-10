module
public import QuantitativeFollowup.StandardSKPosteriorLemma

@[expose] public section

/-! The revised posterior lemma includes the degenerate floor s = 0.
The native posterior theorem already permits that endpoint. This
specialization removes the floor condition, since scalarFloor 0 is all
Parisi probability measures. -/

noncomputable section
open Set MeasureTheory QuantitativePaper QuantitativeFollowup

namespace HexagonPaper

/-- The printed posterior statement on its full closed range of floors. -/
theorem posterior_self_overlap_both_models {n : ℕ} (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t s : ℝ) (hβ : β ≠ 0) (ht : t < 1)
    (hs : s ∈ Icc (0 : ℝ) 1) (hμ : μ ∈ scalarFloor s) :
    StandardSKPosteriorTarget n μ β t s ht ∧
      (∀ D : AnisotropicSpinModel n, AnisotropicPosteriorTarget D μ s) ∧
      (anisotropicMeasureSpinPathLaw (standardSKAnisotropicModel n β t hβ ht) μ s).map
        standardSKMarkedCompression = vectorMeasureSpinPathLaw μ β t s ht.le :=
  followup_posterior_self_overlap_both_models hn μ β t s hβ ht hs hμ

/-- At floor zero the same actual marked-law theorem holds for every profile. -/
theorem posterior_self_overlap_zero {n : ℕ} (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t : ℝ) (hβ : β ≠ 0) (ht : t < 1) :
    StandardSKPosteriorTarget n μ β t 0 ht ∧
      (∀ D : AnisotropicSpinModel n, AnisotropicPosteriorTarget D μ 0) ∧
      (anisotropicMeasureSpinPathLaw (standardSKAnisotropicModel n β t hβ ht) μ 0).map
        standardSKMarkedCompression = vectorMeasureSpinPathLaw μ β t 0 ht.le := by
  apply posterior_self_overlap_both_models hn μ β t 0 hβ ht
  · norm_num
  · simp only [scalarFloor_zero, mem_univ]

end HexagonPaper
