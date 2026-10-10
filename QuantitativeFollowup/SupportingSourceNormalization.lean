module
public import QuantitativeFollowup.FoundationDecomposition
public import QuantitativeFollowup.ReflectedFunctionalRegularization
public import QuantitativeFollowup.VectorCubicLayercake

@[expose] public section

/-! Literal clock, energy-profile and integrated-observable notation from
the follow-up introduction. These definitions use the actual constructed
measure and marked diffusion; they do not assert a response estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory QuantitativePaper
namespace QuantitativeFollowup
variable {n : ℕ}

def followupSourceTime (rho : ℝ) : ℝ := 1-rho
def followupSourceCovariance (β rho : ℝ) : ℝ := β^2*rho
def followupSourceScale (n : ℕ) (β rho : ℝ) : ℝ :=
  (n:ℝ)*followupSourceCovariance β rho

def followupSourceEnergyProfile (μ : Paper.ParisiMeasure) (β q : ℝ) : ℝ :=
  β*Paper.parisiCDF μ q

def followupSourceEnergyFreeMeasure (μ : Paper.ParisiMeasure) (β lam : ℝ) :
    Measure Paper.Overlap := ENNReal.ofReal β • parisiFreeMeasure μ (lam/β)

def followupSourceMeanCovarianceIntegral (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : ℝ :=
  ∫q,foundationMeanCovariance (n:=n) μ β t a ht q ∂parisiFreeMeasure μ a

def followupSourceMeanVarianceIntegral (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : ℝ :=
  ∫q,variance (vectorSelfOverlap (n:=n) μ β t ht q)
    (vectorMeasureSpinPathLaw μ β t a ht) ∂parisiFreeMeasure μ a

def followupSourceCubicIntegral (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : ℝ :=
  ∫q,(∫z,|vectorSelfOverlap (n:=n) μ β t ht q z-(q:ℝ)|^3
    ∂vectorMeasureSpinPathLaw μ β t a ht) ∂parisiFreeMeasure μ a

theorem followupSourceScale_literal (n : ℕ) (β rho : ℝ) :
    followupSourceScale n β rho=(n:ℝ)*(β^2*rho) := rfl

theorem followupSourceEnergyFunctional_literal (n : ℕ) (β lam rho : ℝ)
    (μ : Paper.ParisiMeasure) :
    followupEnergyFunctional n β lam rho μ=
      vectorMeasureFunctional n μ β (followupSourceTime rho) (lam/β)/β := rfl

end QuantitativeFollowup
