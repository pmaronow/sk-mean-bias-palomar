module
public import QuantitativeFollowup.FoundationDecomposition
public import QuantitativePaper.VectorMeanOverlapDifferentiation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

@[expose] public section

/-! The actual mean self-overlap has a C1 extension across both endpoints.
Its derivative is the physical expected squared Hessian, with the literal
normalization c/N.  The extension is obtained from the proved evolution law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem foundation_mean_overlap_contDiff (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) : ContDiff ℝ 1 (vectorMeanOverlapPrimitive (n:=n) μ β t a ht) := by
  apply contDiff_one_iff_deriv.mpr
  refine ⟨fun q => (hasDerivAt_vectorMeanOverlapPrimitive μ β t a ht q).differentiableAt, ?_⟩
  have he : deriv (vectorMeanOverlapPrimitive (n:=n) μ β t a ht) =
      fun q => vectorMeanOverlapDerivative (n:=n) μ β t a ht (projIcc 0 1 zero_le_one q) :=
    funext fun q => (hasDerivAt_vectorMeanOverlapPrimitive μ β t a ht q).deriv
  rw [he]
  exact continuous_vectorMeanOverlapDerivativeReal μ β t a ht

theorem foundation_mean_overlap_derivative (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t ≤ 1) (q : Paper.Overlap) :
    HasDerivAt (vectorMeanOverlapPrimitive (n:=n) μ β t a ht)
      (((1-t)*β^2)/(n:ℝ) *
        (∫p : VectorDisorderBrownianSample n × Configuration n,
          Matrix.trace (vectorMeasureHessianMatrix μ β t ht q p.1 *
            vectorMeasureHessianMatrix μ β t ht q p.1)
          ∂vectorMeasureSpinPathLaw μ β t a ht)) (q:ℝ) := by
  have hd := hasDerivAt_vectorMeanOverlapPrimitive (n:=n) μ β t a ht (q:ℝ)
  rw [projIcc_of_mem zero_le_one q.property] at hd
  simp_rw [vectorMeasureHessianMatrix_trace_square]
  change HasDerivAt (vectorMeanOverlapPrimitive (n:=n) μ β t a ht)
    (((1-t)*β^2)/(n:ℝ) * (∫p : VectorDisorderBrownianSample n × Configuration n,
      vectorMeasureHessianEnergy μ β t ht q p.1 ∂vectorMeasureSpinPathLaw μ β t a ht)) (q:ℝ)
  rw [integral_vectorMeasureSpinPathLaw_sample μ β t a ht _
    (measurable_vectorMeasureHessianEnergy μ β t ht q)]
  exact hd

theorem foundation_mean_overlap_C1_extension (hn : 0 < n)
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) :
    ContDiff ℝ 1 (vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le) ∧
    (∀q : Paper.Overlap, vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le q =
      ∫p, vectorSelfOverlap (n:=n) μ β t ht.le q p
        ∂vectorMeasureSpinPathLaw μ β t a ht.le) ∧
    (∀q : Paper.Overlap,
      HasDerivAt (vectorMeanOverlapPrimitive (n:=n) μ β t a ht.le)
        (((1-t)*β^2)/(n:ℝ) *
          (∫p : VectorDisorderBrownianSample n × Configuration n,
            Matrix.trace (vectorMeasureHessianMatrix μ β t ht.le q p.1 *
              vectorMeasureHessianMatrix μ β t ht.le q p.1)
            ∂vectorMeasureSpinPathLaw μ β t a ht.le)) (q:ℝ)) := by
  refine ⟨foundation_mean_overlap_contDiff μ β t a ht.le, ?_,
    foundation_mean_overlap_derivative μ β t a ht.le⟩
  intro q
  rw [integral_vectorSelfOverlap_eq_mean hn μ β t a ht.le q,
    vectorMeanOverlapPrimitive_eq μ β t a hβ ht q.property]
  change vectorMeanOverlap (n:=n) μ β t a ht.le (projIcc 0 1 zero_le_one (q:ℝ)) = _
  rw [projIcc_of_mem zero_le_one q.property]

end QuantitativeFollowup
