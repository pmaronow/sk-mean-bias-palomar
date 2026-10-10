module
public import QuantitativePaper.VectorDerivativeStability
public import QuantitativePaper.VectorControlExpectedRemainder
public import FourPapersCommon.OneSidedRemainder

@[expose] public section

/-! The actual one-sided weighted control envelope for arbitrary Parisi
probability measures. Feedback continuity and Taylor errors are proved inputs,
not assumptions of the derivative theorem. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorWeightedMeasureControlDerivative (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (Z : VectorDisorderBrownianSample n → ℝ) : ℝ :=
  ∫sample,Z sample*vectorAffineControlDerivative μ ν β t
    (vectorMeasureFeedbackControl μ β t ht) 0 sample ∂vectorDisorderBrownianMeasure n

def vectorControlEnvelopeError (n : ℕ) (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (C : ℝ≥0) (lam : ℝ) : ℝ :=
  (C : ℝ)*(4*(n : ℝ)^2*((1-t)*β^2)^2)*lam +
    (C : ℝ)*vectorControlDerivativeStabilityConstant n β t*
      vectorFeedbackStabilityModulus n β t (Paper.parisiCDFDistance (Paper.parisiMix μ ν lam) μ)

theorem vectorControlEnvelopeError_nonneg (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t ≤ 1) (C : ℝ≥0) (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    0 ≤ vectorControlEnvelopeError n μ ν β t C lam := by
  have hD := Paper.parisiCDFDistance_nonneg (Paper.parisiMix μ ν lam) μ
  have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
  have ht0 : 0 ≤ 1-t := sub_nonneg.mpr ht
  have hlam0 := hlam.1
  unfold vectorControlEnvelopeError vectorControlDerivativeStabilityConstant vectorFeedbackStabilityModulus
  positivity

theorem tendsto_vectorControlEnvelopeError (μ ν : Paper.ParisiMeasure) (β t : ℝ) (C : ℝ≥0) :
    Tendsto (vectorControlEnvelopeError n μ ν β t C)
      (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := by
  have hlam0 : Tendsto (fun lam : ℝ => lam) (𝓝[Icc (0 : ℝ) 1] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hD := tendsto_parisiCDFDistance_mix_left μ ν
  have hc : Continuous (vectorFeedbackStabilityModulus n β t) := by
    unfold vectorFeedbackStabilityModulus; fun_prop
  have hH := hc.continuousAt.tendsto.comp hD
  have hzero : vectorFeedbackStabilityModulus n β t 0 = 0 := by simp [vectorFeedbackStabilityModulus]
  rw [hzero] at hH
  unfold vectorControlEnvelopeError
  simpa only [Function.comp_def,mul_zero,add_zero] using
    (hlam0.const_mul ((C : ℝ)*(4*(n : ℝ)^2*((1-t)*β^2)^2))).add
      (hH.const_mul ((C : ℝ)*vectorControlDerivativeStabilityConstant n β t))

theorem vectorMeasurePotential_mix_weighted_control_remainder
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) (hZn : ∀sample,0 ≤ Z sample)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1) :
    ‖(∫sample,Z sample*vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0
      ∂vectorDisorderBrownianMeasure n)-
      (∫sample,Z sample*vectorMeasurePotential μ β t sample.1 0 ∂vectorDisorderBrownianMeasure n)-
      lam*vectorWeightedMeasureControlDerivative μ ν β t ht Z‖ ≤
      lam*vectorControlEnvelopeError n μ ν β t C lam := by
  let A := vectorMeasureFeedbackControl (n := n) μ β t ht
  let B := vectorMeasureFeedbackControl (n := n) (Paper.parisiMix μ ν lam) β t ht
  have hA : IsVectorParisiControl A := isVectorParisiControl_vectorMeasureFeedbackControl _ β t ht
  have hB : IsVectorParisiControl B := isVectorParisiControl_vectorMeasureFeedbackControl _ β t ht
  let J := fun control ρ => vectorWeightedParisiControlObjective ρ β t control Z
  let V := fun ρ => ∫sample,Z sample*vectorMeasurePotential ρ β t sample.1 0 ∂vectorDisorderBrownianMeasure n
  let DA := vectorWeightedMeasureControlDerivative μ ν β t ht Z
  let DB := ∫sample,Z sample*vectorAffineControlDerivative μ ν β t B 0 sample ∂vectorDisorderBrownianMeasure n
  let Q := (C : ℝ)*(4*(n : ℝ)^2*((1-t)*β^2)^2)
  let H := vectorFeedbackStabilityModulus n β t (Paper.parisiCDFDistance (Paper.parisiMix μ ν lam) μ)
  let L := (C : ℝ)*vectorControlDerivativeStabilityConstant n β t
  have hH : 0 ≤ H := by
    have hD := Paper.parisiCDFDistance_nonneg (Paper.parisiMix μ ν lam) μ
    have hc : 0 ≤ (1-t)*β^2 := mul_nonneg (sub_nonneg.mpr ht) (sq_nonneg _)
    have ht0 : 0 ≤ 1-t := sub_nonneg.mpr ht
    dsimp only [H,vectorFeedbackStabilityModulus]; positivity
  have hL : 0 ≤ L := by dsimp only [L,vectorControlDerivativeStabilityConstant]; positivity
  have hoptA : J A μ = V μ := vectorWeightedParisiControlObjective_feedback_eq_value μ β t ht Z hZ C hC
  have hoptB : J B (Paper.parisiMix μ ν lam) = V (Paper.parisiMix μ ν lam) :=
    vectorWeightedParisiControlObjective_feedback_eq_value _ β t ht Z hZ C hC
  have hupperA : J A (Paper.parisiMix μ ν lam) ≤ V (Paper.parisiMix μ ν lam) :=
    vectorWeightedParisiControlObjective_le_value _ β t ht A hA Z hZ C hC hZn
  have hupperB : J B μ ≤ V μ := vectorWeightedParisiControlObjective_le_value μ β t ht B hB Z hZ C hC hZn
  have hZg : Measurable Z := hZ.mono ((vectorBrownianFiltration n).le 0) le_rfl
  have hremA := vectorWeightedParisiControlObjective_mix_remainder_le μ ν β t ht A hA Z hZg C hC lam hlam
  have hremB := vectorWeightedParisiControlObjective_mix_remainder_le μ ν β t ht B hB Z hZg C hC lam hlam
  have hd := integral_vectorAffineControlDerivative_control_sub_le μ ν β t B A hB hA H hH
    (fun r hr sample => norm_vectorMeasureFeedbackControl_sub_le _ μ β t ht r hr sample) Z hZg C hC
  have hlow : -(Q*lam^2) ≤ J A (Paper.parisiMix μ ν lam)-J A μ-lam*DA :=
    neg_le_of_abs_le (by simpa only [Real.norm_eq_abs,J,Q,DA,vectorWeightedMeasureControlDerivative,A] using hremA)
  have hhigh : J B (Paper.parisiMix μ ν lam)-J B μ-lam*DB ≤ Q*lam^2 :=
    le_of_abs_le (by simpa only [Real.norm_eq_abs,J,Q,DB] using hremB)
  have hdiff : DB-DA ≤ L*H := le_of_abs_le (by
    simpa only [Real.norm_eq_abs,DB,DA,L,vectorWeightedMeasureControlDerivative,A] using hd)
  rw [hoptA] at hlow
  rw [hoptB] at hhigh
  have hmul := mul_le_mul_of_nonneg_left hdiff hlam.1
  have hnon : 0 ≤ lam*L*H := mul_nonneg (mul_nonneg hlam.1 hL) hH
  change ‖V (Paper.parisiMix μ ν lam)-V μ-lam*DA‖ ≤ _
  rw [Real.norm_eq_abs,abs_le]
  unfold vectorControlEnvelopeError
  dsimp only [Q,L,H] at *
  constructor <;> nlinarith

theorem hasDerivWithinAt_vectorMeasurePotential_mix_weighted_control
    (μ ν : Paper.ParisiMeasure) (β t : ℝ) (ht : t ≤ 1)
    (Z : VectorDisorderBrownianSample n → ℝ)
    (hZ : Measurable[vectorBrownianFiltration n 0] Z)
    (C : ℝ≥0) (hC : ∀sample,‖Z sample‖ ≤ C) (hZn : ∀sample,0 ≤ Z sample) :
    HasDerivWithinAt (fun lam => ∫sample,Z sample*vectorMeasurePotential (Paper.parisiMix μ ν lam) β t sample.1 0
      ∂vectorDisorderBrownianMeasure n) (vectorWeightedMeasureControlDerivative μ ν β t ht Z)
      (Icc (0 : ℝ) 1) 0 := by
  apply hasDerivWithinAt_Icc_zero_of_error_bound
    (error := vectorControlEnvelopeError n μ ν β t C)
    (he := tendsto_vectorControlEnvelopeError μ ν β t C)
    (hn := vectorControlEnvelopeError_nonneg μ ν β t ht C)
  intro lam hlam
  simpa only [Paper.parisiMix_zero] using
    vectorMeasurePotential_mix_weighted_control_remainder μ ν β t ht Z hZ C hC hZn lam hlam

end QuantitativePaper
