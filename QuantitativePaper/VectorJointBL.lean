module
public import QuantitativePaper.VectorPosteriorBL
public import QuantitativePaper.VectorOverlapGauge

@[expose] public section

/-! Actual Brascamp--Lieb control of the full joint overlap-score variance.
The passage from a spin slice to the full law uses the proved gauge symmetry,
including the vanishing between-spin term. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup

theorem vectorJoint_weightedOverlap_brascamp_lieb {n k : ℕ} (s : RSBScheme k)
    (β t a : ℝ) (hq : s.q 1=0) (ha : a ≤ s.m 1) (kernel : ℝ → ℝ)
    (σ : Configuration n) :
    variance (fun p : VectorGaussianSpace n k × Configuration n =>
      vectorEuclideanWeightedOverlapScore s β t a kernel p.2 p.1)
      (vectorEuclideanJointLaw s β t a) ≤
      ∫ x, inner ℝ (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) x)
        ((Ring.inverse (hessianOperator (vectorPosteriorPotential s β t a σ) x))
          (gradient (vectorEuclideanWeightedOverlapScore s β t a kernel σ) x))
        ∂vectorSpinPosteriorLaw s β t a σ := by
  rw [variance_vectorEuclideanWeightedOverlapScore_eq_posterior s β t a hq kernel σ]
  exact vectorSpinPosterior_weightedOverlap_brascamp_lieb s β t a hq ha kernel σ

end QuantitativePaper
