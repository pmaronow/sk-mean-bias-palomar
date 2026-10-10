module
public import QuantitativePaper.VectorFiniteControlTelescope
public import QuantitativePaper.VectorNonnegativeTimeIntegral

@[expose] public section

/-! Literal quadratic control cost and actual CDF L1 mismatch on physical
time, with all Bochner integrability discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 600000
variable {n : ℕ}

def vectorParisiControlCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  c/2*Paper.parisiCDF μ r*‖A r sample‖^2

def vectorParisiControlIntegratedCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ∫r in Ioc 0 1,vectorParisiControlCost c μ A r sample ∂nonnegativeLebesgueMeasure

theorem measurable_vectorParisiControlCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorParisiControlCost c μ A)) := by
  have hμ : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n => Paper.parisiCDF μ z.1) :=
    (Paper.parisiCDF_monotone μ).measurable.comp
      (NNReal.continuous_coe.measurable.comp measurable_fst)
  exact (measurable_const.mul hμ).mul (hA.measurable.norm.pow_const 2)

theorem norm_vectorParisiControlCost_le (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorParisiControlCost c μ A r sample‖≤|c| /2*(n : ℝ) := by
  have hA2 : ‖A r sample‖^2≤(n : ℝ) := by
    nlinarith [hA.norm_le r sample,Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg (A r sample)]
  rw [vectorParisiControlCost,Real.norm_eq_abs]
  simp only [abs_mul,abs_div,abs_of_nonneg (by norm_num : (0 : ℝ)≤2),
    abs_of_nonneg (Paper.parisiCDF_nonneg μ r),abs_pow,abs_norm]
  calc
    _ ≤ (|c| /2*1)*(n : ℝ) := by gcongr;exact Paper.parisiCDF_le_one μ r
    _ = _ := by ring

theorem integrableOn_vectorParisiControlCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (sample : VectorDisorderBrownianSample n) :
    IntegrableOn (fun r=>vectorParisiControlCost c μ A r sample) (Ioc 0 1) nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := |c| /2*(n : ℝ))).mono'
    (measurable_vectorParisiControlCost c μ A hA).of_uncurry_right.aestronglyMeasurable
  exact Eventually.of_forall (fun r=>norm_vectorParisiControlCost_le c μ A hA r sample)

theorem integrable_vectorParisiControlIntegratedCost (c : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Integrable (vectorParisiControlIntegratedCost c μ A) (vectorDisorderBrownianMeasure n) := by
  apply integrable_vectorBoundedCellIntegral _ (measurable_vectorParisiControlCost c μ A hA)
    0 1 (|c| /2*(n : ℝ)).toNNReal
  intro r sample
  rw [Real.coe_toNNReal _ (by positivity)]
  exact norm_vectorParisiControlCost_le c μ A hA r sample

theorem integral_nnreal_CDF_abs_sub (μ ν : Paper.ParisiMeasure) :
    (∫r in Ioc (0 : ℝ≥0) 1,|Paper.parisiCDF μ r-Paper.parisiCDF ν r|
      ∂nonnegativeLebesgueMeasure)=Paper.parisiCDFDistance μ ν := by
  have hm : Measurable (fun x : ℝ=>|Paper.parisiCDF μ x-Paper.parisiCDF ν x|) :=
    ((Paper.parisiCDF_monotone μ).measurable.sub (Paper.parisiCDF_monotone ν).measurable).abs
  have hh := vectorNonnegativeTimeIntegral_eq_interval _ hm (1 : ℝ≥0)
  change (∫r in Ioc (0 : ℝ≥0) 1,|Paper.parisiCDF μ r-Paper.parisiCDF ν r|
    ∂nonnegativeLebesgueMeasure)=(∫r in (0 : ℝ)..1,|Paper.parisiCDF μ r-Paper.parisiCDF ν r|) at hh
  rw [hh]
  simp only [Paper.parisiCDFDistance,Real.norm_eq_abs]

theorem integrableOn_nnreal_CDF_abs_sub (μ ν : Paper.ParisiMeasure) :
    IntegrableOn (fun r : ℝ≥0=>|Paper.parisiCDF μ r-Paper.parisiCDF ν r|)
      (Ioc 0 1) nonnegativeLebesgueMeasure := by
  apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := (1 : ℝ))).mono'
    ((((Paper.parisiCDF_monotone μ).measurable.sub (Paper.parisiCDF_monotone ν).measurable).abs).comp
      NNReal.continuous_coe.measurable).aestronglyMeasurable
  exact Eventually.of_forall (fun r=>by
    change ‖|Paper.parisiCDF μ r-Paper.parisiCDF ν r|‖≤1
    rw [Real.norm_eq_abs,abs_abs]
    exact abs_le.mpr ⟨by linarith [Paper.parisiCDF_nonneg μ r,Paper.parisiCDF_le_one ν r],
      by linarith [Paper.parisiCDF_le_one μ r,Paper.parisiCDF_nonneg ν r]⟩)

end QuantitativePaper
