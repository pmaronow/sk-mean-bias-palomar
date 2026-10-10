module
public import QuantitativePaper.VectorDyadicTerminalSpinPairing

@[expose] public section

/-! The actual arbitrary-profile terminal Gibbs spin has conditional
mean equal to the actual Parisi gradient along its Wiener diffusion. This
is obtained from genuine finite-cell identities and actual tilted limits. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem measurable_vectorDyadicSpinMean_component (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (l : Fin n) :
    Measurable (fun sample : VectorDisorderBrownianSample n=>
      vectorDyadicSpinMean μ β t ht q j sample l) := by
  have hm := (measurable_vectorBackwardMean
    (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t
    (fun σ=>Paper.spinSign (σ l)) (vectorDyadicTimeIndex q j)).comp
    (measurable_vectorFiniteJointState
      (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht (vectorDyadicTime q j))
  convert hm using 1
  funext sample
  exact vectorDyadicSpinMean_eq_backward μ β t ht q j sample l

theorem vectorMeasure_terminal_spin_pairing_past (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (l : Fin n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀ sample,‖Z sample‖≤C) :
    (∫sample,Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
      (fun σ=>Paper.spinSign (σ l)) ∂vectorMeasureDisorderTilt μ β t a)=
      ∫sample,Z sample*vectorMeasureSpinMean μ β t ht.le q sample l
        ∂vectorMeasureDisorderTilt μ β t a := by
  have hZm : Measurable Z := hZ.mono
    ((vectorBrownianFiltration n).le (q : ℝ).toNNReal) le_rfl
  have hd : ∀σ : Configuration n,|Paper.spinSign (σ l)|≤(1 : ℝ) :=
    fun σ=>le_of_eq (Paper.abs_spinSign (σ l))
  have hFm (j : ℕ) : Measurable (fun sample : VectorDisorderBrownianSample n=>
      Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>Paper.spinSign (σ l))) := by
    have hφ : Measurable (fun p : VectorState n=>terminalMean
        (vectorTerminalExponent n β t p.1 p.2) (fun σ=>Paper.spinSign (σ l))) :=
      (continuous_vectorTerminalMean_joint β t (fun σ=>Paper.spinSign (σ l))).measurable
    have hψ : Measurable (fun sample : VectorDisorderBrownianSample n=>
        (sample.1,vectorDyadicState μ β t ht.le j 1 sample)) :=
      measurable_vectorFiniteJointState (n:=n)
        (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t ht.le 1
    have hf := hφ.comp hψ
    dsimp only [Function.comp_def] at hf
    exact hZm.fun_mul hf
  have hFb (j : ℕ) (sample : VectorDisorderBrownianSample n) :
      ‖Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>Paper.spinSign (σ l))‖≤C := by
    rw [norm_mul]
    have hb : ‖terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>Paper.spinSign (σ l))‖≤1 := by
      simpa only [Real.norm_eq_abs] using terminalMean_bound _ _ 1 hd
    calc
      _ ≤ ‖Z sample‖*1 := mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ ≤ C := by simpa only [mul_one] using hC sample
  have hFt (sample : VectorDisorderBrownianSample n) :
      Tendsto (fun j=>Z sample*terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>Paper.spinSign (σ l))) atTop
        (𝓝 (Z sample*terminalMean
          (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
          (fun σ=>Paper.spinSign (σ l)))) := by
    have hX := tendsto_vectorDyadicState_at_moving_time μ β t ht.le 1 (fun _=>1)
      (fun _=>le_rfl) tendsto_const_nhds sample
    have hp : Tendsto (fun _ : ℕ=>sample.1) atTop (𝓝 sample.1) := tendsto_const_nhds
    have he : Tendsto (fun j=>terminalMean
        (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
        (fun σ=>Paper.spinSign (σ l))) atTop
        (𝓝 (terminalMean
          (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
          (fun σ=>Paper.spinSign (σ l)))) := by
      change Tendsto
        ((fun p : VectorState n=>terminalMean
          (vectorTerminalExponent n β t p.1 p.2) (fun σ=>Paper.spinSign (σ l))) ∘
          (fun j=>(sample.1,vectorDyadicState μ β t ht.le j 1 sample))) atTop
        (𝓝 (terminalMean
          (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
          (fun σ=>Paper.spinSign (σ l))))
      have hraw := ((continuous_vectorTerminalMean_joint β t
        (fun σ=>Paper.spinSign (σ l))).tendsto
          (sample.1,vectorMeasureState μ β t ht.le 1 sample)).comp (hp.prodMk_nhds hX)
      dsimp only [Function.comp_def] at hraw
      exact hraw
    exact he.const_mul (Z sample)
  have hleft := tendsto_integral_vectorDyadicTilt_bounded μ β t a ht.le
    (fun j sample=>Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorDyadicState μ β t ht.le j 1 sample))
      (fun σ=>Paper.spinSign (σ l)))
    (fun sample=>Z sample*terminalMean
      (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht.le 1 sample))
      (fun σ=>Paper.spinSign (σ l))) C C.coe_nonneg
    hFm hFb (.of_forall hFt)
  have hright := tendsto_integral_vectorDyadicTilt_bounded μ β t a ht.le
    (fun j sample=>Z sample*vectorDyadicSpinMean μ β t ht.le q j sample l)
    (fun sample=>Z sample*vectorMeasureSpinMean μ β t ht.le q sample l) C C.coe_nonneg
    (fun j=>hZm.fun_mul (measurable_vectorDyadicSpinMean_component μ β t ht.le q j l))
    (fun j sample=>by
      rw [norm_mul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left
        (vectorDyadicSpinMean_component_bound μ β t ht.le q j sample l)
        (norm_nonneg _)).trans (by simpa only [mul_one] using hC sample))
    (.of_forall fun sample=>by
      have he := (EuclideanSpace.proj l).continuous.tendsto
        (vectorMeasureSpinMean μ β t ht.le q sample) |>.comp
          (tendsto_vectorDyadicSpinMean μ β t ht.le q sample)
      have he' : Tendsto (fun j=>vectorDyadicSpinMean μ β t ht.le q j sample l) atTop
          (𝓝 (vectorMeasureSpinMean μ β t ht.le q sample l)) := he
      exact he'.const_mul (Z sample))
  apply tendsto_nhds_unique hleft
  exact hright.congr' (.of_forall fun j=>
    (vectorDyadic_terminal_spin_pairing_past μ β t a hβ ht q j l Z hZ C hC).symm)

end QuantitativePaper
