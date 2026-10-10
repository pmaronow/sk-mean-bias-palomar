module
public import QuantitativePaper.VectorDyadicDirectionalVariance

@[expose] public section

/-! The actual finite conditional covariance sandwich survives arbitrary
bounded nonnegative tests of the entire Wiener past. No strong covariance
convergence is needed: the terminal second moment is tested backwards. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1600000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

private theorem bounded_weight_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Z F : Ω→ℝ) (hZ : Measurable Z)
    (hF : Measurable F) (C R : ℝ) (hC : ∀x,‖Z x‖≤C) (hR : ∀x,‖F x‖≤R) :
    Integrable (fun x=>Z x*F x) P := by
  apply Integrable.of_bound (hZ.fun_mul hF).aestronglyMeasurable (C*R)
  exact .of_forall fun x=>by
    rw [norm_mul]
    exact mul_le_mul (hC x) (hR x) (norm_nonneg _) (le_trans (norm_nonneg (Z x)) (hC x))

theorem integral_vectorDyadic_directionalVariance (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorDyadicDirectionalVariance μ β t ht.le q j w sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)=
      (∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>(fieldDot w σ)^2)
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)-
      ∫sample,Z sample*(vectorDyadicMeanInDirection μ β t ht.le q j w sample)^2
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
  let s:=Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let P:=vectorFiniteDisorderTilt (n:=n) s β t a
  letI:=vectorFiniteDisorderTilt_probability (n:=n) s β t a
  let B:=fun sample : VectorDisorderBrownianSample n=>vectorBackwardMean s β t
    (fun σ=>(fieldDot w σ)^2) (vectorDyadicTimeIndex q j)
    (vectorFiniteJointState s β t ht.le (vectorDyadicTime q j) sample)
  have hZm : Measurable Z:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hd (σ : Configuration n) : |(fieldDot w σ)^2|≤(vectorDirectionBound w)^2 := by
    rw [abs_sq]
    have he:=mul_self_le_mul_self (abs_nonneg _) (abs_fieldDot_le_directionBound w σ)
    simpa only [←pow_two,sq_abs] using he
  have hB : Measurable B:=(measurable_vectorBackwardMean s β t _ _).comp
    (measurable_vectorFiniteJointState s β t ht.le (vectorDyadicTime q j))
  have hBb (sample) : ‖B sample‖≤(vectorDirectionBound w)^2 := by
    simpa only [Real.norm_eq_abs] using abs_vectorBackwardMean_le s β t _ _ hd _ _
  have hBi:=bounded_weight_product_integrable P Z B hZm hB C _ hC hBb
  have hMi:=bounded_weight_product_integrable P Z
    (fun sample=>(vectorDyadicMeanInDirection μ β t ht.le q j w sample)^2) hZm
    ((measurable_vectorDyadicMeanInDirection μ β t ht.le q j w).pow_const 2) C
    ((vectorDirectionBound w)^2) hC (fun sample=>by
      simp only [Real.norm_eq_abs,abs_sq]
      have he:=mul_self_le_mul_self (abs_nonneg _)
        (vectorDyadicMeanInDirection_bound μ β t ht.le q j w sample)
      simpa only [←pow_two,sq_abs] using he)
  have he : (fun sample=>Z sample*vectorDyadicDirectionalVariance μ β t ht.le q j w sample)=
      fun sample=>Z sample*B sample-Z sample*(vectorDyadicMeanInDirection μ β t ht.le q j w sample)^2 := by
    funext sample
    rw [vectorDyadicDirectionalVariance_eq_secondMoment_sub]
    change Z sample*(B sample-_)=_
    ring
  rw [he,integral_sub hBi hMi]
  rw [vectorDyadic_secondMoment_pairing_past μ β t a hβ ht q j w Z hZ C hC]

theorem tendsto_integral_vectorDyadicTilt_directionalVariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    Tendsto (fun j=>∫sample,Z sample*vectorDyadicDirectionalVariance μ β t ht.le q j w sample
      ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a) atTop
      (𝓝 ((∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
        (fun σ=>(fieldDot w σ)^2) ∂vectorMeasureDisorderTilt μ β t a)-
      ∫sample,Z sample*(vectorMeasureMeanInDirection μ β t ht.le q w sample)^2
        ∂vectorMeasureDisorderTilt μ β t a)) := by
  have hZm : Measurable Z:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hd (σ : Configuration n) : |(fieldDot w σ)^2|≤(vectorDirectionBound w)^2 := by
    rw [abs_sq]
    have he:=mul_self_le_mul_self (abs_nonneg _) (abs_fieldDot_le_directionBound w σ)
    simpa only [←pow_two,sq_abs] using he
  have hT:=tendsto_integral_vectorDyadicTilt_terminal_mean μ β t a ht.le
    (fun σ=>(fieldDot w σ)^2) ((vectorDirectionBound w)^2) (sq_nonneg _) hd Z hZm C C.coe_nonneg hC
  have hM:=tendsto_integral_vectorDyadicTilt_mean_square μ β t a ht.le q w Z hZm C hC
  simpa only [integral_vectorDyadic_directionalVariance μ β t a hβ ht q _ w Z hZ C hC] using hT.sub hM

theorem vectorMeasure_weighted_hessian_variance_bounds (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) (hZn : ∀sample,0≤Z sample) :
    let V:=(∫sample,Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
        (fun σ=>(fieldDot w σ)^2) ∂vectorMeasureDisorderTilt μ β t a)-
      ∫sample,Z sample*(vectorMeasureMeanInDirection μ β t ht.le q w sample)^2
        ∂vectorMeasureDisorderTilt μ β t a
    Paper.parisiCDF μ q*V≤∫sample,Z sample*vectorMeasureHessianQuadratic μ β t ht.le q w sample
      ∂vectorMeasureDisorderTilt μ β t a ∧
    (∫sample,Z sample*vectorMeasureHessianQuadratic μ β t ht.le q w sample
      ∂vectorMeasureDisorderTilt μ β t a)≤V := by
  dsimp only
  have hZm : Measurable Z:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hV:=tendsto_integral_vectorDyadicTilt_directionalVariance μ β t a hβ ht q w Z hZ C hC
  have hH:=tendsto_integral_vectorDyadicTilt_hessian_quadratic μ β t a ht.le q w Z hZm C hC
  have hFin (j : ℕ) :
      vectorDyadicNodeMass μ q j*(∫sample,Z sample*vectorDyadicDirectionalVariance μ β t ht.le q j w sample
        ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)≤
        ∫sample,Z sample*vectorDyadicHessianQuadratic μ β t ht.le q j w sample
          ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a ∧
      (∫sample,Z sample*vectorDyadicHessianQuadratic μ β t ht.le q j w sample
          ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a)≤
        ∫sample,Z sample*vectorDyadicDirectionalVariance μ β t ht.le q j w sample
          ∂vectorFiniteDisorderTilt (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a := by
    let P:=vectorFiniteDisorderTilt (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
    letI:=vectorFiniteDisorderTilt_probability (n:=n) (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t a
    have hVi:=bounded_weight_product_integrable P Z _ hZm
      (measurable_vectorDyadicDirectionalVariance μ β t ht.le q j w) C ((vectorDirectionBound w)^2) hC
      (fun sample=>by simpa only [Real.norm_eq_abs] using vectorDyadicDirectionalVariance_bound μ β t ht.le q j w sample)
    have hHi:=bounded_weight_product_integrable P Z _ hZm
      (measurable_vectorDyadicHessianQuadratic μ β t ht.le q j w) C ((n : ℝ)*‖w‖^2) hC
      (fun sample=>by simpa only [Real.norm_eq_abs] using vectorDyadicHessianQuadratic_bound μ β t ht.le q j w sample)
    constructor
    · rw [←integral_const_mul]
      exact integral_mono (hVi.const_mul _) hHi (fun sample=>by
        have he:=mul_le_mul_of_nonneg_left
          (vectorDyadicHessian_directionalVariance_bounds μ β t ht.le q j w sample).1 (hZn sample)
        simpa only [mul_left_comm] using he)
    · exact integral_mono hHi hVi (fun sample=>mul_le_mul_of_nonneg_left
        (vectorDyadicHessian_directionalVariance_bounds μ β t ht.le q j w sample).2 (hZn sample))
  exact ⟨le_of_tendsto_of_tendsto ((tendsto_vectorDyadicNodeMass μ q).mul hV) hH
      (.of_forall fun j=>(hFin j).1),
    le_of_tendsto_of_tendsto hH hV (.of_forall fun j=>(hFin j).2)⟩

end QuantitativePaper
