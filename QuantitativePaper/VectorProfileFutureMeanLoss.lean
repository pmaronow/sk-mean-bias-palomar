module
public import QuantitativePaper.VectorGridFutureIntegral

@[expose] public section

/-! The genuine arbitrary-profile future Hessian identity, paired with
every bounded observable of the entire earlier disorder/Brownian past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 2000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorDyadic_future_mean_loss (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*vectorDyadicHessianQuadratic μ β t ht.le q j w p
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) +
      vectorDyadicNodeMass μ q j *
        (∫p, Z p*(vectorDyadicMeanInDirection μ β t ht.le q j w p)^2
          ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) +
      vectorDyadicFutureMeanSquareTail μ β t a ht.le q j w Z =
      ∫p, Z p*terminalMean (vectorTerminalExponent n β t p.1
        (vectorDyadicState μ β t ht.le j 1 p)) (fun σ => (fieldDot w σ)^2)
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  let s := Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  have hi : vectorDyadicTimeIndex q j ≤ (vectorDyadicIndex j+1)+2 :=
    (vectorDyadicTimeIndex_le q j).trans (by omega)
  have htime : (s.q (vectorDyadicTimeIndex q j)).toNNReal = vectorDyadicTime q j := by
    rw [vectorDyadicTimeIndex_node]
    rfl
  have hpast : Measurable[vectorBrownianFiltration n (s.q (vectorDyadicTimeIndex q j)).toNNReal] Z := by
    rw [htime]
    exact hZ.mono ((vectorBrownianFiltration n).mono (le_vectorDyadicTime q j)) le_rfl
  have he := vectorFinite_future_mean_loss s β t a hβ ht (vectorDyadicTimeIndex q j) hi w Z hpast C hC
  rw [htime] at he
  dsimp only [s] at he
  simp_rw [←vectorDyadicMeanInDirection_eq_backward μ β t ht.le q j w] at he
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hfuture := vectorGrid_future_mean_sum_eq_integral μ β t a ht.le q j w Z hZm
  rw [←hfuture]
  simpa only [vectorDyadicHessianQuadratic, vectorDyadicNodeMass, vectorDyadicState,
    Nat.add_assoc] using he

theorem vectorMeasure_future_mean_loss (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β ≠ 0) (ht : t < 1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀p, ‖Z p‖ ≤ C) :
    (∫p, Z p*vectorMeasureHessianQuadratic μ β t ht.le q w p
      ∂vectorMeasureDisorderTilt μ β t a) +
      Paper.parisiCDF μ q *
        (∫p, Z p*(vectorMeasureMeanInDirection μ β t ht.le q w p)^2
          ∂vectorMeasureDisorderTilt μ β t a) +
      vectorMeasureFutureMeanSquareTail μ β t a ht.le q w Z =
      ∫p, Z p*terminalMean (vectorTerminalExponent n β t p.1
        (vectorMeasureState μ β t ht.le 1 p)) (fun σ => (fieldDot w σ)^2)
        ∂vectorMeasureDisorderTilt μ β t a := by
  have hZm : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hH := tendsto_integral_vectorDyadicTilt_hessian_quadratic μ β t a ht.le q w Z hZm C hC
  have hM := tendsto_integral_vectorDyadicTilt_mean_square μ β t a ht.le q w Z hZm C hC
  have hF := tendsto_vectorDyadicFutureMeanSquareTail μ β t a ht.le q w Z hZm C hC
  have hsum := (hH.add ((tendsto_vectorDyadicNodeMass μ q).mul hM)).add hF
  have hd (σ : Configuration n) : |(fieldDot w σ)^2| ≤ (vectorDirectionBound w)^2 := by
    rw [abs_sq]
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (abs_fieldDot_le_directionBound w σ) 2
  have hT := tendsto_integral_vectorDyadicTilt_terminal_mean μ β t a ht.le
    (fun σ => (fieldDot w σ)^2) ((vectorDirectionBound w)^2) (sq_nonneg _) hd Z hZm
    C C.coe_nonneg hC
  exact tendsto_nhds_unique hsum (hT.congr' (.of_forall fun j =>
    (vectorDyadic_future_mean_loss μ β t a hβ ht q j w Z hZ C hC).symm))

end QuantitativePaper
