module
public import QuantitativePaper.VectorDyadicDirectionalMoments
public import QuantitativePaper.VectorMeasureSpinPast
public import Mathlib.Probability.CondVar
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Actual arbitrary-profile directional conditional covariance, built from
the terminal Gibbs second moment and the actual adapted spin mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology BigOperators
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorMeasureTerminalSecondMoment (μ : Paper.ParisiMeasure) (β t : ℝ) (ht : t≤1)
    (w : Field n) (sample : VectorDisorderBrownianSample n) : ℝ :=
  terminalMean (vectorTerminalExponent n β t sample.1 (vectorMeasureState μ β t ht 1 sample))
    (fun σ=>fieldDot w σ^2)

def vectorMeasureConditionalVariance (μ : Paper.ParisiMeasure) (β t a : ℝ) (ht : t≤1)
    (q : Paper.Overlap) (w : Field n) : VectorDisorderBrownianSample n→ℝ :=
  (vectorMeasureDisorderTilt μ β t a)[vectorMeasureTerminalSecondMoment μ β t ht w |
      vectorBrownianFiltration n (q:ℝ).toNNReal]-
    (fun sample=>(vectorMeasureMeanInDirection μ β t ht q w sample)^2)

theorem measurable_vectorMeasureTerminalSecondMoment (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (w : Field n) : Measurable (vectorMeasureTerminalSecondMoment μ β t ht w) := by
  have hφ : Measurable (fun p : VectorState n=>terminalMean
      (vectorTerminalExponent n β t p.1 p.2) (fun σ=>fieldDot w σ^2)) :=
    (continuous_vectorTerminalMean_joint β t (fun σ=>fieldDot w σ^2)).measurable
  have hh:=hφ.comp (measurable_vectorMeasureJointState μ β t ht 1)
  dsimp only [Function.comp_def,vectorMeasureJointState] at hh
  exact hh

theorem norm_vectorMeasureTerminalSecondMoment_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    ‖vectorMeasureTerminalSecondMoment μ β t ht w sample‖≤(vectorDirectionBound w)^2 := by
  rw [Real.norm_eq_abs]
  apply terminalMean_bound _ _ _
  intro σ
  rw [abs_sq]
  have hb:=abs_fieldDot_le_directionBound w σ
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (fieldDot w σ)) hb 2

theorem integrable_vectorMeasureTerminalSecondMoment (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (w : Field n) :
    Integrable (vectorMeasureTerminalSecondMoment μ β t ht w) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  exact (integrable_const ((vectorDirectionBound w)^2)).mono'
    (measurable_vectorMeasureTerminalSecondMoment μ β t ht w).aestronglyMeasurable
    (.of_forall fun sample=>norm_vectorMeasureTerminalSecondMoment_le μ β t ht w sample)

theorem integrable_vectorMeasureMeanInDirection_sq (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    Integrable (fun sample=>(vectorMeasureMeanInDirection μ β t ht q w sample)^2)
      (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  have hm:Measurable (vectorMeasureMeanInDirection μ β t ht q w):=
    (adapted_vectorMeasureMeanInDirection μ β t ht q w).mono ((vectorBrownianFiltration n).le _) le_rfl
  apply (integrable_const ((vectorDirectionBound w)^2)).mono' (hm.pow_const 2).aestronglyMeasurable
  filter_upwards with sample
  rw [Real.norm_eq_abs,abs_sq]
  have hb:=vectorMeasureMeanInDirection_bound μ β t ht q w sample
  simpa only [sq_abs] using pow_le_pow_left₀
    (abs_nonneg (vectorMeasureMeanInDirection μ β t ht q w sample)) hb 2

theorem stronglyMeasurable_vectorMeasureConditionalVariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    StronglyMeasurable[vectorBrownianFiltration n (q:ℝ).toNNReal]
      (vectorMeasureConditionalVariance μ β t a ht q w) :=
  stronglyMeasurable_condExp.sub
    (((adapted_vectorMeasureMeanInDirection μ β t ht q w).pow_const 2).stronglyMeasurable)

theorem integrable_vectorMeasureConditionalVariance (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    Integrable (vectorMeasureConditionalVariance μ β t a ht q w) (vectorMeasureDisorderTilt μ β t a) :=
  integrable_condExp.sub (integrable_vectorMeasureMeanInDirection_sq μ β t a ht q w)

theorem integral_vectorMeasureConditionalVariance_mul_past (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (ht : t≤1) (q : Paper.Overlap) (w : Field n)
    (Z : VectorDisorderBrownianSample n→ℝ)
    (hZ : Measurable[vectorBrownianFiltration n (q:ℝ).toNNReal] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖≤C) :
    (∫sample,Z sample*vectorMeasureConditionalVariance μ β t a ht q w sample
      ∂vectorMeasureDisorderTilt μ β t a)=
      (∫sample,Z sample*vectorMeasureTerminalSecondMoment μ β t ht w sample
        ∂vectorMeasureDisorderTilt μ β t a)-
      ∫sample,Z sample*(vectorMeasureMeanInDirection μ β t ht q w sample)^2
        ∂vectorMeasureDisorderTilt μ β t a := by
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  let V:=vectorBrownianFiltration n (q:ℝ).toNNReal
  have hm:=hZ.mono ((vectorBrownianFiltration n).le _) le_rfl
  have hb : ∀ᵐ sample∂P,‖Z sample‖≤(C:ℝ):=.of_forall hC
  have hsecond:=integrable_vectorMeasureTerminalSecondMoment μ β t a ht w
  have hproduct : Integrable (fun sample=>Z sample*vectorMeasureTerminalSecondMoment μ β t ht w sample) P := by
    simpa only [mul_comm] using hsecond.mul_bdd hm.aestronglyMeasurable hb
  have hpull:=condExp_mul_of_stronglyMeasurable_left hZ.stronglyMeasurable hproduct hsecond (m:=V)
  have he:=integral_congr_ae hpull
  rw [integral_condExp ((vectorBrownianFiltration n).le _)] at he
  simp only [Pi.mul_apply] at he
  have hi1 : Integrable (fun sample=>Z sample*(P[vectorMeasureTerminalSecondMoment μ β t ht w|V]) sample) P := by
    simpa only [mul_comm] using (integrable_condExp (f:=vectorMeasureTerminalSecondMoment μ β t ht w)
      (μ:=P) (m:=V)).mul_bdd hm.aestronglyMeasurable hb
  have hi2 : Integrable (fun sample=>Z sample*(vectorMeasureMeanInDirection μ β t ht q w sample)^2) P := by
    simpa only [mul_comm] using
      (integrable_vectorMeasureMeanInDirection_sq μ β t a ht q w).mul_bdd hm.aestronglyMeasurable hb
  change (∫sample,Z sample*((P[vectorMeasureTerminalSecondMoment μ β t ht w|V]) sample-
    (vectorMeasureMeanInDirection μ β t ht q w sample)^2)∂P)=_
  simp_rw [mul_sub]
  rw [integral_sub hi1 hi2,←he]

end QuantitativePaper
