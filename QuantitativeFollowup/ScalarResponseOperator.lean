module
public import QuantitativeFollowup.ScalarFutureDiagonal
public import QuantitativeFollowup.ScalarSpinConditional
public import QuantitativeFollowup.ParisiFreeMeasure

@[expose] public section

/-! The paper's literal seven-term scalar response operator, evaluated
under the constructed Brownian diffusion and the actual marked spin law.
This is a definition of J, not a theorem that it is the transport response;
that identification and its operator order require separate proofs. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper FourPapersCommon FRSB
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 800000

def scalarFutureDerivativePairing (β : ℝ) (μ : Paper.ParisiMeasure)
    (p ell : Paper.Overlap) : ℝ :=
  if h : (p : ℝ) ≤ ell then
    ∫ ω,M β μ p ω*scalarFutureSquareDerivative β μ p ell h
      (parisiPhysicalSplitState β 0 μ p ω) ∂canonicalBrownianMeasure
  else 0

def scalarFutureCenteredPairing (β : ℝ) (μ : Paper.ParisiMeasure)
    (p r ell : Paper.Overlap) : ℝ :=
  if h : (r : ℝ) ≤ ell then
    ∫ ω,scalarCenteredSquare β μ p ω*scalarFutureSquareProcess β μ r ell h ω ∂canonicalBrownianMeasure
  else 0

/-- Literal display `eq:scalarJexplicit`: no response or domination conclusion is built
into the definition.  The strict future intervals retain the right-CDF convention. -/
def scalarResponseOperator (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (s : ℝ)
    (φ : Paper.Overlap → ℝ) (p : Paper.Overlap) : ℝ :=
  β^2*(
    (∫ ω,C β μ p ω^2+2*(1-parisiCDF μ p)*M β μ p ω^2*C β μ p ω ∂canonicalBrownianMeasure)*φ p
    -(∫ ell in Ioi p,scalarFutureDerivativePairing β μ p ell*φ ell ∂parisiFreeMeasure μ s)
    -2*(∫ r,(∫ ω,M β μ p ω*C β μ p ω*M β μ r ω ∂canonicalBrownianMeasure)*φ (min p r)
      ∂parisiFreeMeasure μ s)
    -(∫ r,(∫ z,scalarCenteredSquare β μ p z.1*Paper.spinSign z.2*M β μ r z.1
      ∂scalarMarkedSpinLaw β hβ μ)*φ r ∂parisiFreeMeasure μ s)
    +(1/2:ℝ)*(∫ r,parisiCDF μ r*(∫ ω,scalarCenteredSquare β μ p ω*M β μ r ω^2
      ∂canonicalBrownianMeasure)*φ r ∂parisiFreeMeasure μ s)
    +(1/2:ℝ)*(∫ r,∫ ell,(∫ ω,scalarCenteredSquare β μ p ω*M β μ r ω*M β μ ell ω
      ∂canonicalBrownianMeasure)*φ (min r ell) ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s)
    +(1/2:ℝ)*(∫ r,∫ ell in Ioi r,scalarFutureCenteredPairing β μ p r ell*φ ell
      ∂parisiFreeMeasure μ s ∂parisiFreeMeasure μ s))

/-- Compression to scalar transports fixing both endpoint levels. -/
def scalarCompressedResponse (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (s : ℝ)
    (φ : Paper.Overlap → ℝ) (p : Paper.Overlap) : ℝ :=
  if (p : ℝ)=0 ∨ (p : ℝ)=1 then 0 else scalarResponseOperator β hβ μ s φ p

theorem scalarCompressedResponse_endpoints (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) (φ : Paper.Overlap → ℝ) :
    scalarCompressedResponse β hβ μ s φ ⟨0,by norm_num⟩=0 ∧
      scalarCompressedResponse β hβ μ s φ ⟨1,by norm_num⟩=0 := by
  simp [scalarCompressedResponse]

end QuantitativeFollowup
