module
public import QuantitativePaper.VectorDyadicGridAgreement
public import QuantitativePaper.VectorMeasureSpatialSmooth
public import QuantitativePaper.VectorFiniteMeasureStateStability
public import FRSB.GridMeasureIdentification

@[expose] public section

/-! Literal spatial-jet and same-driver diffusion agreement for nested grid laws. -/
noncomputable section
open MeasureTheory Set FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets QuantitativeFollowup
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorMeasureGradient_grid_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasureGradient (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q p x =
      vectorFiniteTailGradient (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t q p x := by
  rw [vectorMeasureGradient_eq_gradient, vectorMeasureTailPotential_grid_eq_finite μ a β t ht q p]
  · rfl
  · exact ht

theorem vectorMeasureTailPotential_grid_jet_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (r : ℕ) :
    iteratedFDeriv ℝ r (vectorMeasureTailPotential (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q p) =
      iteratedFDeriv ℝ r (vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a))
        β t q p (vectorDyadicIndex a+3)) := by
  rw [vectorMeasureTailPotential_grid_eq_finite μ a β t ht q p]

theorem vectorMeasureHessian_grid_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (p : Couplings n × ℝ) (x : Field n) :
    vectorMeasureHessian (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q p x =
      hessianOperator (vectorTailRecursion (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a))
        β t q p (vectorDyadicIndex a+3)) x := by
  unfold vectorMeasureHessian
  rw [vectorMeasureTailPotential_grid_eq_finite μ a β t ht q p]

theorem vectorMeasureState_grid_eq_finite (μ : Paper.ParisiMeasure) (a : ℕ)
    (β t : ℝ) (ht : t ≤ 1) (r : NNReal) (hr : r ≤ 1) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureState (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t ht r sample =
      vectorFiniteState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t ht r sample := by
  have hg : ∀ q p x, ‖vectorMeasureGradient (n := n)
      (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) β t q p x -
        vectorFiniteTailGradient (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a)) β t q p x‖ ≤ 0 := by
    intro q p x
    rw [vectorMeasureGradient_grid_eq_finite μ a β t ht q p x, sub_self, norm_zero]
  have h := norm_vectorMeasureState_sub_finite_le
    (Paper.parisiGridMeasure μ (vectorDyadicIndex a)) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex a))
    β t ht 0 le_rfl hg r hr sample
  rw [FRSB.parisiSchemeMeasure_grid_eq] at h
  simp only [Paper.parisiCDFDistance, sub_self, abs_zero, intervalIntegral.integral_zero,
    mul_zero, add_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

end QuantitativePaper
