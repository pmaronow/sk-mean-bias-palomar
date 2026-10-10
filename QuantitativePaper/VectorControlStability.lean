module
public import QuantitativePaper.VectorControlRemainder

@[expose] public section

/-! Genuine same-control-coordinate stability estimates for literal vector
control states and costs. All integral bounds use the actual CDF. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

theorem norm_vectorControlledState_control_sub_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A B : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (hB : IsVectorParisiControl B)
    (ε : ℝ) (hε : 0 ≤ ε) (sample : VectorDisorderBrownianSample n)
    (hb : ∀r ≤ (1 : ℝ≥0),‖A r sample-B r sample‖ ≤ ε) :
    ‖vectorControlledState c μ A 1 sample-vectorControlledState c μ B 1 sample‖ ≤ |c| *ε := by
  have hiA := integrableOn_vectorControlDrift c μ A hA 1 sample
  have hiB := integrableOn_vectorControlDrift c μ B hB 1 sample
  have he := integral_sub hiA hiB
  unfold vectorControlledState vectorIntegratedDrift
  rw [add_sub_add_left_eq_sub,← he]
  have hh := norm_setIntegral_le_of_norm_le_const
    (f := fun r => vectorControlDrift c μ A r sample-vectorControlDrift c μ B r sample)
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1))
    (fun r (hr : r ∈ Ioc (0 : ℝ≥0) 1) => by
      rw [vectorControlDrift,vectorControlDrift,← smul_sub,norm_smul,Real.norm_eq_abs,
        abs_mul,abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
      exact mul_le_mul ((mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one μ r) (abs_nonneg c)).trans_eq (mul_one _))
        (hb r hr.2) (norm_nonneg _) (abs_nonneg c))
  simpa only [Measure.real,nonnegativeLebesgueMeasure_Ioc,NNReal.coe_zero,NNReal.coe_one,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using hh

theorem vectorParisiControlCost_control_sub_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A B : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (hB : IsVectorParisiControl B)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorParisiControlCost c μ A r sample-vectorParisiControlCost c μ B r sample‖ ≤
      |c| *Real.sqrt (n : ℝ)*‖A r sample-B r sample‖ := by
  have hN : |‖A r sample‖-‖B r sample‖| ≤ ‖A r sample-B r sample‖ := abs_norm_sub_norm_le _ _
  have hS : |‖A r sample‖+‖B r sample‖| ≤ 2*Real.sqrt (n : ℝ) := by
    rw [abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    linarith [hA.norm_le r sample,hB.norm_le r sample]
  have hsq : |‖A r sample‖^2-‖B r sample‖^2| ≤
      ‖A r sample-B r sample‖*(2*Real.sqrt (n : ℝ)) := by
    rw [sq_sub_sq,abs_mul]
    calc
      _ ≤ (2*Real.sqrt (n : ℝ))*‖A r sample-B r sample‖ :=
        mul_le_mul hS hN (abs_nonneg _) (by positivity)
      _ = _ := by ring
  unfold vectorParisiControlCost
  rw [← mul_sub,Real.norm_eq_abs,abs_mul,abs_mul,abs_div,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg (Paper.parisiCDF_nonneg μ r)]
  calc
    _ ≤ (|c|/2*1)*(‖A r sample-B r sample‖*(2*Real.sqrt (n : ℝ))) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (Paper.parisiCDF_le_one μ r) (by positivity)
      · exact hsq
      · exact abs_nonneg _
      · positivity
    _ = _ := by ring

theorem norm_vectorParisiControlIntegratedCost_control_sub_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A B : ℝ≥0 → VectorDisorderBrownianSample n → Field n)
    (hA : IsVectorParisiControl A) (hB : IsVectorParisiControl B)
    (ε : ℝ) (hε : 0 ≤ ε) (sample : VectorDisorderBrownianSample n)
    (hb : ∀r ≤ (1 : ℝ≥0),‖A r sample-B r sample‖ ≤ ε) :
    ‖vectorParisiControlIntegratedCost c μ A sample-vectorParisiControlIntegratedCost c μ B sample‖ ≤
      |c| *Real.sqrt (n : ℝ)*ε := by
  unfold vectorParisiControlIntegratedCost
  rw [← integral_sub (integrableOn_vectorParisiControlCost c μ A hA sample)
    (integrableOn_vectorParisiControlCost c μ B hB sample)]
  have hh := norm_setIntegral_le_of_norm_le_const
    (lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1))
    (fun r (hr : r ∈ Ioc (0 : ℝ≥0) 1) =>
      (vectorParisiControlCost_control_sub_le c μ A B hA hB r sample).trans
        (mul_le_mul_of_nonneg_left (hb r hr.2) (by positivity)))
  simpa only [Measure.real,nonnegativeLebesgueMeasure_Ioc,NNReal.coe_zero,NNReal.coe_one,
    sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,mul_one] using hh

end QuantitativePaper
