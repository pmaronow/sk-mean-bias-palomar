module
public import QuantitativePaper.VectorFutureAtomicIntegral
public import QuantitativePaper.VectorDyadicGridJetAgreement
public import QuantitativePaper.VectorDyadicDirectionalMoments

@[expose] public section

/-! Actual uniform-grid geometry and the exact identification of future
node magnetizations with the arbitrary-profile diffusion for its grid law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory FourPapersCommon
open scoped NNReal BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem vectorGrid_future_node_order (μ : Paper.ParisiMeasure) (j i : ℕ)
    (hi0 : 0 < i) (hi : i ≤ j+2) (p : Fin (j+2)) :
    (Paper.parisiGridRSBScheme μ j).q i <
        (Paper.parisiGridRSBScheme μ j).q (p+1) ↔ i < (p:ℕ)+1 := by
  change ((min (i-1) (j+1):ℕ):ℝ) / (j+1:ℕ) <
    ((min ((p:ℕ)+1-1) (j+1):ℕ):ℝ) / (j+1:ℕ) ↔ _
  have hi' : i-1 ≤ j+1 := by omega
  have hp : (p:ℕ) ≤ j+1 := by omega
  simp only [Nat.add_sub_cancel, min_eq_left hi', min_eq_left hp]
  rw [div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < (j+1:ℕ))]
  rw [Nat.cast_lt]
  omega

theorem vectorProfileRound_gridPoint (j : ℕ) (p : Fin (j+2)) :
    Paper.parisiGridRound j (Paper.parisiGridPoint j p) = Paper.parisiGridPoint j p := by
  apply Subtype.ext
  change (Nat.ceil ((j+1:ℕ)*((p:ℝ)/(j+1:ℕ))):ℝ)/(j+1:ℕ) = (p:ℝ)/(j+1:ℕ)
  have hd : (j+1:ℝ) ≠ 0 := by positivity
  have he : (j+1:ℕ)*((p:ℝ)/(j+1:ℕ)) = (p:ℝ) := by field_simp
  rw [he]
  simp only [Nat.ceil_natCast]

theorem vectorProfileRound_idem (j : ℕ) (q : Paper.Overlap) :
    Paper.parisiGridRound j (Paper.parisiGridRound j q) = Paper.parisiGridRound j q :=
  vectorProfileRound_gridPoint j (Paper.parisiGridIndex j q)

theorem vectorMeasureMeanInDirection_grid_eq_dyadic (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    vectorMeasureMeanInDirection (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      β t ht (Paper.parisiGridRound (vectorDyadicIndex j) q) w sample =
      vectorDyadicMeanInDirection μ β t ht q j w sample := by
  unfold vectorMeasureMeanInDirection vectorDyadicMeanInDirection
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  unfold vectorMeasureSpinMean vectorDyadicSpinMean
  rw [vectorMeasureState_grid_eq_finite μ j β t ht _
      (by change vectorDyadicTime q j ≤ 1; exact vectorDyadicTime_le_one q j) sample,
    vectorMeasureGradient_grid_eq_finite μ j β t ht]
  rfl

theorem vectorMeasureMeanInDirection_grid_node (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t ≤ 1) (j i : ℕ) (hi : i ≤ vectorDyadicIndex j+3)
    (w : Field n) (sample : VectorDisorderBrownianSample n) :
    vectorMeasureMeanInDirection (Paper.parisiGridMeasure μ (vectorDyadicIndex j))
      β t ht ⟨(Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i,
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_nonneg hi,
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_le_one hi⟩ w sample =
      vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
        (fun σ => fieldDot w σ) i
        (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
          ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q i).toNNReal sample) := by
  rw [vectorBackwardMean_fieldDot]
  unfold vectorMeasureMeanInDirection
  apply Finset.sum_congr rfl
  intro l _
  congr 1
  unfold vectorMeasureSpinMean vectorFiniteJointState
  rw [vectorMeasureState_grid_eq_finite μ j β t ht _
      (Real.toNNReal_le_one.mpr ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q_le_one hi)) sample,
    vectorMeasureGradient_grid_eq_finite μ j β t ht,
    vectorFiniteTailGradient_at_node _ β t i (by omega)]

end QuantitativePaper
