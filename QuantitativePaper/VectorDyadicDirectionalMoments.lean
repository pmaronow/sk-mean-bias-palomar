module
public import QuantitativePaper.VectorDyadicHessianPassage
public import QuantitativePaper.VectorMeasureGradientAdaptation
public import QuantitativePaper.VectorBackwardLinear

@[expose] public section

/-! Genuine directional spin means and bounded terminal-observable
expectation limits under the actual fractional disorder tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorDirectionBound (w : Field n) : ℝ := ∑l : Fin n,|w l|

theorem vectorDirectionBound_nonneg (w : Field n) : 0≤vectorDirectionBound w :=
  Finset.sum_nonneg fun _ _=>abs_nonneg _

theorem abs_fieldDot_le_directionBound (w : Field n) (σ : Configuration n) :
    |fieldDot w σ|≤vectorDirectionBound w := by
  unfold fieldDot vectorDirectionBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum fun l _=>by rw [abs_mul,Paper.abs_spinSign,mul_one]

def vectorDyadicMeanInDirection (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑l : Fin n,w l*vectorDyadicSpinMean μ β t ht q j sample l

def vectorMeasureMeanInDirection (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∑l : Fin n,w l*vectorMeasureSpinMean μ β t ht q sample l

theorem measurable_vectorDyadicMeanInDirection (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) :
    Measurable (vectorDyadicMeanInDirection μ β t ht q j w) :=
  Finset.measurable_sum Finset.univ fun l _=>
    (measurable_vectorDyadicSpinMean_component μ β t ht q j l).const_mul _

theorem adapted_vectorMeasureMeanInDirection (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (vectorMeasureMeanInDirection μ β t ht q w) :=
  Finset.measurable_sum Finset.univ fun l _=>
    (adapted_vectorMeasureSpinMean_component μ β t ht q l).const_mul _

theorem vectorDyadicMeanInDirection_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    |vectorDyadicMeanInDirection μ β t ht q j w sample|≤vectorDirectionBound w := by
  unfold vectorDyadicMeanInDirection vectorDirectionBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (vectorDyadicSpinMean_component_bound μ β t ht q j sample l)
    (abs_nonneg _)).trans_eq (mul_one _)

theorem vectorMeasureMeanInDirection_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    |vectorMeasureMeanInDirection μ β t ht q w sample|≤vectorDirectionBound w := by
  unfold vectorMeasureMeanInDirection vectorDirectionBound
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left (vectorMeasureSpinMean_component_bound μ β t ht q sample l)
    (abs_nonneg _)).trans_eq (mul_one _)

theorem tendsto_vectorDyadicMeanInDirection (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    Tendsto (fun j=>vectorDyadicMeanInDirection μ β t ht q j w sample) atTop
      (𝓝 (vectorMeasureMeanInDirection μ β t ht q w sample)) := by
  apply tendsto_finset_sum
  intro l _
  have he : Tendsto (fun j=>vectorDyadicSpinMean μ β t ht q j sample l) atTop
      (𝓝 (vectorMeasureSpinMean μ β t ht q sample l)) :=
    (EuclideanSpace.proj l).continuous.tendsto _ |>.comp
      (tendsto_vectorDyadicSpinMean μ β t ht q sample)
  exact he.const_mul _

theorem vectorDyadicMeanInDirection_eq_backward (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    vectorDyadicMeanInDirection μ β t ht q j w sample=
      vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
        (fun σ=>fieldDot w σ) (vectorDyadicTimeIndex q j)
        (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
          (vectorDyadicTime q j) sample) := by
  unfold vectorDyadicMeanInDirection
  simp_rw [vectorDyadicSpinMean_eq_backward,vectorBackwardMean_spin]
  exact (vectorBackwardMean_fieldDot _ β t _ _ w).symm

theorem tendsto_integral_vectorDyadicTilt_terminal_mean (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (d : Configuration n→ℝ) (R : ℝ) (hR : 0≤R) (hd : ∀σ,|d σ|≤R)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ) (hC : 0≤C) (hZb : ∀sample,‖Z sample‖≤C) :
    Tendsto (fun j=>∫sample,Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht j 1 sample)) d
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 (∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample)) d
        ∂vectorMeasureDisorderTilt μ β t a)) := by
  have hφ : Measurable (fun p : VectorState n=>terminalMean (vectorTerminalExponent n β t p.1 p.2) d) :=
    (continuous_vectorTerminalMean_joint β t d).measurable
  have hFj (j : ℕ) : Measurable (fun sample : VectorDisorderBrownianSample n=>
      Z sample*terminalMean (vectorTerminalExponent n β t sample.1
        (vectorDyadicState μ β t ht j 1 sample)) d) := by
    have hf:=hφ.comp (measurable_vectorFiniteJointState
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht 1)
    dsimp only [Function.comp_def] at hf
    exact hZ.fun_mul hf
  apply tendsto_integral_vectorDyadicTilt_bounded μ β t a ht _ _ (C*R) (mul_nonneg hC hR) hFj
  · intro j sample
    rw [norm_mul]
    have hb : ‖terminalMean (vectorTerminalExponent n β t sample.1
        (vectorDyadicState μ β t ht j 1 sample)) d‖≤R := by
      simpa only [Real.norm_eq_abs] using terminalMean_bound _ d R hd
    exact mul_le_mul (hZb sample) hb (norm_nonneg _) hC
  · exact .of_forall fun sample=>by
      have hX:=tendsto_vectorDyadicState_at_moving_time μ β t ht 1 (fun _=>1)
        (fun _=>le_rfl) tendsto_const_nhds sample
      have hp : Tendsto (fun _ : ℕ=>sample.1) atTop (𝓝 sample.1) := tendsto_const_nhds
      have he:=(continuous_vectorTerminalMean_joint β t d).tendsto _ |>.comp (hp.prodMk_nhds hX)
      dsimp only [Function.comp_def] at he
      exact he.const_mul (Z sample)

end QuantitativePaper
