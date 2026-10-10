module
public import QuantitativePaper.VectorFutureCovarianceMatrix

@[expose] public section

/-! The covariance integral on the actual marked terminal-spin probability
space, using its proved disorder/Brownian marginal and whole-past law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal
namespace QuantitativePaper
variable {n : ℕ}

theorem vectorMeasureHessianMatrix_physical_future_covariance_integral
    (μ : Paper.ParisiMeasure) (β t a : ℝ) (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) :
    ∀ᵐp ∂vectorMeasureSpinPathLaw (n:=n) μ β t a ht.le, ∀i j : Fin n,
      vectorMeasureHessianMatrix μ β t ht.le q p.1 i j =
        Paper.parisiCDF μ q*vectorMeasureSpinCovariance μ β t a ht.le q p.1 i j +
        ∫u : Paper.Overlap,
          if q < u then vectorMeasureExpectedFutureCovarianceMatrix μ β t a q ht.le u p.1 i j else 0
            ∂(μ:Measure Paper.Overlap) :=
  (measurePreserving_vectorMeasureSpinPathLaw_fst μ β t a ht.le).quasiMeasurePreserving.ae
    (vectorMeasureHessianMatrix_future_covariance_integral μ β t a hβ ht q)

end QuantitativePaper
