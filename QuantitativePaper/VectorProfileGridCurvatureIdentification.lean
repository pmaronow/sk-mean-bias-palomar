module
public import QuantitativePaper.VectorProfileGridResponseIdentification
public import QuantitativePaper.VectorProfileClosedTraceSquare

@[expose] public section

/-! The true closed-cell physical curvature observable is exactly the
arbitrary-measure curvature for the actual common-grid mixture. -/
noncomputable section
open Set MeasureTheory
open scoped NNReal
namespace QuantitativePaper
open SpinGlass.Targets FourPapersCommon QuantitativeFollowup
set_option maxHeartbeats 2800000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 300000
variable {n : ℕ}

theorem vectorProfile_grid_retained_curvature_expected (hn : 0<n)
    (μ ν : Paper.ParisiMeasure) (j : ℕ) (β t lam θ : ℝ) (ht : t≤1)
    (hθ : θ∈Icc (0:ℝ) 1) (i : ℕ) (hi : i≤vectorDyadicIndex j+2) (q : Paper.Overlap)
    (hq : (q:ℝ)∈Icc ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i)
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q (i+1))) :
    vectorProfileRetainedExpectation (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
      (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t (lam/β) θ ht hθ
      (vectorProfileRetainedTraceSquare (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i) q=
      (n:ℝ)*responseAveragedCurvature (n:=n)
        (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t lam ht q:=by
  have hq1 : (q:ℝ).toNNReal≤1:=by
    simpa only [Real.toNNReal_one] using Real.toNNReal_le_toNNReal q.property.2
  have heScheme:=vector_grid_profile_scheme_eq_mix μ ν (vectorDyadicIndex j) θ hθ
  unfold vectorProfileRetainedExpectation
  rw [heScheme]
  dsimp only
  rw [←vectorMeasureDisorderTilt_grid_eq_finite (Paper.parisiMix μ ν θ) j β t (lam/β) ht]
  simp_rw [←vectorMeasureState_grid_eq_finite (Paper.parisiMix μ ν θ) j β t ht (q:ℝ).toNNReal hq1]
  have he : (fun sample : VectorDisorderBrownianSample n=>
      vectorProfileRetainedTraceSquare (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j))
        (Paper.parisiGridRSBScheme ν (vectorDyadicIndex j)) β t i q
        ((θ,sample.1),vectorMeasureState (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t ht (q:ℝ).toNNReal sample))=
      (fun sample=>β^2*vectorMeasureHessianEnergy
        (Paper.parisiGridMeasure (Paper.parisiMix μ ν θ) (vectorDyadicIndex j)) β t ht q sample):=by
    funext sample
    unfold vectorProfileRetainedTraceSquare
    rw [vectorProfileCellJointPotential_grid_mix μ ν j β t θ ht hθ i hi q hq sample.1]
    congr 1
    unfold euclideanOperatorTrace
    rw [euclideanOperatorMatrix_mul]
    change Matrix.trace (vectorMeasureHessianMatrix _ β t ht q sample*
      vectorMeasureHessianMatrix _ β t ht q sample)=_
    exact vectorMeasureHessianMatrix_trace_square _ β t ht q sample
  rw [he,integral_const_mul]
  unfold responseAveragedCurvature
  have hn0 : (n:ℝ)≠0:=by exact_mod_cast hn.ne'
  field_simp [hn0]

end QuantitativePaper
