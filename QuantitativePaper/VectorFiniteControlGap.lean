module
public import QuantitativePaper.VectorControlCost

@[expose] public section

/-! Actual finite-profile control gap and the quantitative CDF mismatch
estimate, with no verification or endpoint-law premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 800000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

def vectorFiniteControlGap (s : RSBScheme k) (β t : ℝ) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  vectorTerminalPotential n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)-
    vectorRecursion s β t sample.1 (k+2) 0-
    vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample

theorem integrable_vectorFiniteControlGap (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Integrable (vectorFiniteControlGap s β t μ A) (vectorDisorderBrownianMeasure n) :=
  (vectorFinite_control_verification s β t hβ ht μ A hA).1.sub
    (integrable_vectorParisiControlIntegratedCost _ μ A hA)

theorem vectorFiniteControlGap_integral_eq (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    (∫sample,vectorFiniteControlGap s β t μ A sample ∂vectorDisorderBrownianMeasure n)=
      ∫sample,(∫r in Ioc 0 1,vectorFiniteControlSource s β t μ A r sample-
        vectorParisiControlCost ((1-t)*β^2) μ A r sample ∂nonnegativeLebesgueMeasure)
        ∂vectorDisorderBrownianMeasure n := by
  have he := vectorFinite_control_verification s β t hβ ht μ A hA
  have hcost := integrable_vectorParisiControlIntegratedCost ((1-t)*β^2) μ A hA
  have hsrc := integrable_vectorBoundedCellIntegral _ (measurable_vectorFiniteControlSource s β t μ A hA)
    0 1 (3*|((1-t)*β^2)| *(n : ℝ)).toNNReal (fun r sample=>by
      rw [Real.coe_toNNReal _ (by positivity)]
      exact norm_vectorFiniteControlSource_le s β t μ A hA r sample)
  have hspi (sample : VectorDisorderBrownianSample n) :
      IntegrableOn (fun r=>vectorFiniteControlSource s β t μ A r sample) (Ioc 0 1)
        nonnegativeLebesgueMeasure := by
    apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1)
      (C := 3*|((1-t)*β^2)| *(n : ℝ))).mono'
      (measurable_vectorFiniteControlSource s β t μ A hA).of_uncurry_right.aestronglyMeasurable
    exact Eventually.of_forall (fun r=>norm_vectorFiniteControlSource_le s β t μ A hA r sample)
  refine (show (∫sample,vectorFiniteControlGap s β t μ A sample ∂vectorDisorderBrownianMeasure n)=
      (∫sample,vectorTerminalPotential n β t sample.1
        (vectorControlledState ((1-t)*β^2) μ A 1 sample)-vectorRecursion s β t sample.1 (k+2) 0
        ∂vectorDisorderBrownianMeasure n)-
      (∫sample,vectorParisiControlIntegratedCost ((1-t)*β^2) μ A sample
        ∂vectorDisorderBrownianMeasure n) from by
      simpa only [vectorFiniteControlGap,Pi.sub_apply] using integral_sub he.1 hcost).trans ?_
  rw [he.2]
  refine (integral_sub hsrc hcost).symm.trans ?_
  apply integral_congr_ae
  exact Eventually.of_forall (fun sample=>by
    exact (integral_sub (hspi sample) (integrableOn_vectorParisiControlCost _ μ A hA sample)).symm)

theorem vectorFiniteControlSource_sub_cost_le (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) :
    vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost ((1-t)*β^2) μ A r sample≤
      ((1-t)*β^2)/2*(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r| := by
  let G := vectorFiniteControlGradient s β t μ A r sample
  let c := (1-t)*β^2
  have hc : 0≤c := by dsimp only [c];positivity
  have hG : ‖G‖≤Real.sqrt (n : ℝ) := norm_vectorFiniteTailGradient_le s β t _ _ _
  have hG2 : ‖G‖^2≤(n : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg G]
  have hd : (Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2≤
      |Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r| *(n : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hG2 (abs_nonneg _))
  have hh := mul_le_mul_of_nonneg_left hd (show 0≤c/2 by positivity)
  have hneg : 0≤c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2 :=
    mul_nonneg (mul_nonneg (by positivity) (Paper.parisiCDF_nonneg μ r)) (sq_nonneg _)
  change c/2*Paper.parisiCDF μ r*‖A r sample‖^2-c/2*Paper.parisiCDF μ r*‖G-A r sample‖^2+
    c/2*(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2-
      c/2*Paper.parisiCDF μ r*‖A r sample‖^2≤_
  change _≤c/2*(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|
  linarith

theorem vectorFiniteControlGap_integral_le (s : RSBScheme k) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    (∫sample,vectorFiniteControlGap s β t μ A sample ∂vectorDisorderBrownianMeasure n)≤
      ((1-t)*β^2)/2*(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s) := by
  rw [vectorFiniteControlGap_integral_eq s β t hβ ht μ A hA]
  let w : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample =>
    vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost ((1-t)*β^2) μ A r sample
  have hm : Measurable (Function.uncurry w) :=
    (measurable_vectorFiniteControlSource s β t μ A hA).sub (measurable_vectorParisiControlCost _ μ A hA)
  have hi := integrable_vectorBoundedCellIntegral w hm
    0 1 ((7/2 : ℝ)*|((1-t)*β^2)| *(n : ℝ)).toNNReal (fun r sample=>by
      rw [Real.coe_toNNReal _ (by positivity)]
      change ‖vectorFiniteControlSource s β t μ A r sample-
        vectorParisiControlCost ((1-t)*β^2) μ A r sample‖≤_
      exact (norm_sub_le _ _).trans (by
        have h1 := norm_vectorFiniteControlSource_le s β t μ A hA r sample
        have h2 := norm_vectorParisiControlCost_le ((1-t)*β^2) μ A hA r sample
        linarith))
  have hb (sample : VectorDisorderBrownianSample n) :
      (∫r in Ioc 0 1,vectorFiniteControlSource s β t μ A r sample-
        vectorParisiControlCost ((1-t)*β^2) μ A r sample ∂nonnegativeLebesgueMeasure)≤
      ((1-t)*β^2)/2*(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s) := by
    have hsrc : IntegrableOn (fun r=>vectorFiniteControlSource s β t μ A r sample)
        (Ioc 0 1) nonnegativeLebesgueMeasure := by
      apply (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1)
        (C := 3*|((1-t)*β^2)| *(n : ℝ))).mono'
        (measurable_vectorFiniteControlSource s β t μ A hA).of_uncurry_right.aestronglyMeasurable
      exact Eventually.of_forall (fun r=>norm_vectorFiniteControlSource_le s β t μ A hA r sample)
    have hh := integral_mono (hsrc.sub (integrableOn_vectorParisiControlCost _ μ A hA sample))
      ((integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (((1-t)*β^2)/2*(n : ℝ)))
      (fun r=>vectorFiniteControlSource_sub_cost_le s β t ht.le μ A r sample)
    simpa only [Pi.sub_apply,integral_const_mul,integral_nnreal_CDF_abs_sub] using hh
  exact (integral_mono hi (integrable_const _) hb).trans_eq (by simp)

end QuantitativePaper
