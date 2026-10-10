module
public import QuantitativePaper.VectorMeasureHessianEnergy
public import QuantitativeFollowup.VectorOverlapDeficit

@[expose] public section

/-! A genuine differentiable extension built from the actual continuous
Hessian energy. Equality with the physical second moment is obtained later
from the proved cell telescope; no derivative of a clamped moment is assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace QuantitativePaper
open QuantitativeFollowup
set_option maxHeartbeats 700000
variable {n : ℕ}

def vectorMeanOverlapPrimitive (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : ℝ) : ℝ :=
  vectorMeanOverlapReal (n:=n) μ β t a ht 0+
    ∫r in 0..q,vectorMeanOverlapDerivative (n:=n) μ β t a ht (projIcc (0 : ℝ) 1 zero_le_one r)

theorem continuous_vectorMeanOverlapDerivativeReal (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) : Continuous (fun q : ℝ=>vectorMeanOverlapDerivative (n:=n) μ β t a ht
      (projIcc (0 : ℝ) 1 zero_le_one q)) :=
  (continuous_vectorMeanOverlapDerivative μ β t a ht).comp continuous_projIcc

theorem hasDerivAt_vectorMeanOverlapPrimitive (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : ℝ) : HasDerivAt (vectorMeanOverlapPrimitive (n:=n) μ β t a ht)
      (vectorMeanOverlapDerivative (n:=n) μ β t a ht (projIcc (0 : ℝ) 1 zero_le_one q)) q := by
  have hc:=continuous_vectorMeanOverlapDerivativeReal (n:=n) μ β t a ht
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 q)
    (hc.stronglyMeasurableAtFilter volume (nhds q)) hc.continuousAt).const_add _

def vectorOverlapPotentialPrimitive (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1) (q : ℝ) : ℝ :=
  ∫r in q..1,vectorMeanOverlapPrimitive (n:=n) μ β t a ht r-r

theorem hasDerivAt_vectorOverlapPotentialPrimitive (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : ℝ) : HasDerivAt (vectorOverlapPotentialPrimitive (n:=n) μ β t a ht)
      (q-vectorMeanOverlapPrimitive (n:=n) μ β t a ht q) q := by
  have hc:Continuous (fun r : ℝ=>vectorMeanOverlapPrimitive (n:=n) μ β t a ht r-r):=
    (continuous_iff_continuousAt.mpr fun r=>(hasDerivAt_vectorMeanOverlapPrimitive μ β t a ht r).continuousAt).sub continuous_id
  convert intervalIntegral.integral_hasDerivAt_left (hc.intervalIntegrable q 1)
    (hc.stronglyMeasurableAtFilter volume (nhds q)) hc.continuousAt using 1
  · rfl
  · ring

end QuantitativePaper
