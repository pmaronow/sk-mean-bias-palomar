module
public import QuantitativePaper.VectorDyadicDirectionalMoments
public import QuantitativePaper.VectorMeasureHessianAdaptation
public import QuantitativePaper.VectorFieldConditionalVariance

@[expose] public section

/-! Genuine finite directional variances, their literal Hessian sandwich,
and weighted limits. The whole original Wiener past remains available to
the weight when it is passed to the upward dyadic node. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

def vectorDyadicDirectionalVariance (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (j : ℕ) (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorBackwardVariance (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
    (fun σ=>fieldDot w σ) (vectorDyadicTimeIndex q j)
    (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
      (vectorDyadicTime q j) sample)

theorem measurable_vectorDyadicDirectionalVariance (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n) :
    Measurable (vectorDyadicDirectionalVariance μ β t ht q j w) := by
  unfold vectorDyadicDirectionalVariance vectorBackwardVariance
  have hm:=measurable_vectorFiniteJointState (n:=n)
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht (vectorDyadicTime q j)
  exact ((measurable_vectorBackwardMean _ β t _ _).comp hm).sub
    (((measurable_vectorBackwardMean _ β t _ _).comp hm).pow_const 2)

theorem vectorDyadicDirectionalVariance_nonneg (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    0≤vectorDyadicDirectionalVariance μ β t ht q j w sample := by
  unfold vectorDyadicDirectionalVariance
  rw [vectorBackwardVariance_eq_observableCovariance]
  let R : ℝ≥0:=⟨vectorDirectionBound w,vectorDirectionBound_nonneg w⟩
  exact vectorObservableCovariance_nonneg _ β t _ _ R
    (abs_fieldDot_le_directionBound w) _ _ _

theorem vectorDyadicDirectionalVariance_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    |vectorDyadicDirectionalVariance μ β t ht q j w sample|≤(vectorDirectionBound w)^2 := by
  unfold vectorDyadicDirectionalVariance
  rw [vectorBackwardVariance_eq_observableCovariance]
  let R : ℝ≥0:=⟨vectorDirectionBound w,vectorDirectionBound_nonneg w⟩
  exact abs_vectorObservableCovariance_le _ β t _ _ R
    (abs_fieldDot_le_directionBound w) _ _ _

theorem vectorDyadicHessian_directionalVariance_bounds (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    vectorDyadicNodeMass μ q j*vectorDyadicDirectionalVariance μ β t ht q j w sample≤
      vectorDyadicHessianQuadratic μ β t ht q j w sample ∧
    vectorDyadicHessianQuadratic μ β t ht q j w sample≤
      vectorDyadicDirectionalVariance μ β t ht q j w sample := by
  unfold vectorDyadicDirectionalVariance
  rw [vectorBackwardVariance_eq_observableCovariance]
  exact vectorFieldHessian_covariance_quadratic_bounds _ β t _ _ _ w

theorem vectorDyadicDirectionalVariance_eq_secondMoment_sub (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    vectorDyadicDirectionalVariance μ β t ht q j w sample=
      vectorBackwardMean (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
        (fun σ=>(fieldDot w σ)^2) (vectorDyadicTimeIndex q j)
        (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht
          (vectorDyadicTime q j) sample)-
      (vectorDyadicMeanInDirection μ β t ht q j w sample)^2 := by
  rw [vectorDyadicMeanInDirection_eq_backward]
  rfl

theorem vectorDyadic_secondMoment_pairing_past (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorBackwardMean
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
      (fun σ=>(fieldDot w σ)^2) (vectorDyadicTimeIndex q j)
      (vectorFiniteJointState (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le
        (vectorDyadicTime q j) sample)
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)=
      ∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>(fieldDot w σ)^2)
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  have hi : vectorDyadicTimeIndex q j≤(vectorDyadicIndex j+1)+2 :=
    (vectorDyadicTimeIndex_le q j).trans (by omega)
  have htime : ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q
      (vectorDyadicTimeIndex q j)).toNNReal=vectorDyadicTime q j := by
    rw [vectorDyadicTimeIndex_node]
    rfl
  have hpast : Measurable[vectorBrownianFiltration n
      ((Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)).q
        (vectorDyadicTimeIndex q j)).toNNReal] Z := by
    rw [htime]
    exact hZ.mono ((vectorBrownianFiltration n).mono (le_vectorDyadicTime q j)) le_rfl
  have he:=vectorFinite_terminal_mean_pairing_past
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a hβ ht
    (fun σ=>(fieldDot w σ)^2) (vectorDyadicTimeIndex q j) hi Z hpast C hC
  rw [htime] at he
  exact he.symm

theorem tendsto_integral_vectorDyadicTilt_mean_square (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Tendsto (fun j=>∫sample,Z sample*(vectorDyadicMeanInDirection μ β t ht q j w sample)^2
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 (∫sample,Z sample*(vectorMeasureMeanInDirection μ β t ht q w sample)^2
        ∂vectorMeasureDisorderTilt μ β t a)) := by
  apply tendsto_integral_vectorDyadicTilt_bounded μ β t a ht _ _
    ((C : ℝ)*(vectorDirectionBound w)^2) (mul_nonneg C.coe_nonneg (sq_nonneg _))
  · intro j
    exact hZ.fun_mul ((measurable_vectorDyadicMeanInDirection μ β t ht q j w).pow_const 2)
  · intro j sample
    simp only [norm_mul,Real.norm_eq_abs,abs_sq]
    have hb:=mul_self_le_mul_self (abs_nonneg _)
      (vectorDyadicMeanInDirection_bound μ β t ht q j w sample)
    have hb' : (vectorDyadicMeanInDirection μ β t ht q j w sample)^2≤(vectorDirectionBound w)^2 :=
      by simpa only [←pow_two,sq_abs] using hb
    exact mul_le_mul (hC sample) hb' (sq_nonneg _) C.coe_nonneg
  · exact .of_forall fun sample=>
      ((tendsto_vectorDyadicMeanInDirection μ β t ht q w sample).pow 2).const_mul (Z sample)

theorem tendsto_integral_vectorDyadicTilt_hessian_quadratic (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Tendsto (fun j=>∫sample,Z sample*vectorDyadicHessianQuadratic μ β t ht q j w sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 (∫sample,Z sample*vectorMeasureHessianQuadratic μ β t ht q w sample
        ∂vectorMeasureDisorderTilt μ β t a)) := by
  apply tendsto_integral_vectorDyadicTilt_bounded μ β t a ht _ _
    ((C : ℝ)*((n : ℝ)*‖w‖^2)) (mul_nonneg C.coe_nonneg (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))
  · intro j
    exact hZ.fun_mul (measurable_vectorDyadicHessianQuadratic μ β t ht q j w)
  · intro j sample
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul (hC sample) (vectorDyadicHessianQuadratic_bound μ β t ht q j w sample)
      (abs_nonneg _) C.coe_nonneg
  · exact .of_forall fun sample=>
      (tendsto_vectorDyadicHessianQuadratic μ β t ht q w sample).const_mul (Z sample)

end QuantitativePaper
