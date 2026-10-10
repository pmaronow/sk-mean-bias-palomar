module
public import QuantitativePaper.VectorMeasureControlLimit
public import QuantitativePaper.VectorMildLimit

@[expose] public section

/-! The actual gradient feedback attains the constructed arbitrary-measure
value. Finite-cell square gaps disappear by genuine uniform gradient
convergence; the coefficient error disappears in actual CDF L1. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n k : ℕ}

theorem vectorFiniteControlSource_sub_cost_abs_le (s : RSBScheme k) (β t : ℝ)
    (ht : t≤1) (μ : Paper.ParisiMeasure)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) (ε : ℝ) (hε : 0≤ε)
    (hgap : ‖vectorFiniteControlGradient s β t μ A r sample-A r sample‖≤ε) :
    |vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost ((1-t)*β^2) μ A r sample|≤
      ((1-t)*β^2)/2*(ε^2+(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|) := by
  let G := vectorFiniteControlGradient s β t μ A r sample
  let c := (1-t)*β^2
  have hc : 0≤c/2 := by dsimp only [c];positivity
  have hG : ‖G‖≤Real.sqrt (n : ℝ) := norm_vectorFiniteTailGradient_le s β t _ _ _
  have hG2 : ‖G‖^2≤(n : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg G]
  have hg2 : ‖G-A r sample‖^2≤ε^2 := by nlinarith [norm_nonneg (G-A r sample)]
  have hμ := Paper.parisiCDF_nonneg μ r
  have hμ1 := Paper.parisiCDF_le_one μ r
  have hprod : Paper.parisiCDF μ r*‖G-A r sample‖^2≤ε^2 :=
    (mul_le_mul_of_nonneg_right hμ1 (sq_nonneg _)).trans (by simpa only [one_mul] using hg2)
  have he : vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample=
      c/2*((Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2-
        Paper.parisiCDF μ r*‖G-A r sample‖^2) := by
    unfold vectorFiniteControlSource vectorParisiControlCost
    dsimp only [G,c]
    ring
  rw [he,abs_mul,abs_of_nonneg hc]
  apply mul_le_mul_of_nonneg_left _ hc
  calc
    _ ≤ |(Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r)*‖G‖^2|+
        |Paper.parisiCDF μ r*‖G-A r sample‖^2| := abs_sub _ _
    _ ≤ |Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r| *(n : ℝ)+ε^2 := by
      simp only [abs_mul,abs_pow,abs_norm,abs_of_nonneg hμ]
      exact add_le_add (mul_le_mul_of_nonneg_left hG2 (abs_nonneg _)) hprod
    _ = _ := by ring

theorem vectorFiniteControlGradient_feedback_sub_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (j : ℕ) (r : ℝ≥0) (hr : r≤1) (sample : VectorDisorderBrownianSample n) :
    ‖vectorFiniteControlGradient (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ
      (vectorMeasureFeedbackControl μ β t ht) r sample-vectorMeasureFeedbackControl μ β t ht r sample‖≤
        vectorDyadicGradientError n β t j := by
  unfold vectorFiniteControlGradient
  rw [←vectorMeasureState_eq_controlled μ β t ht r hr sample]
  unfold vectorMeasureFeedbackControl
  change dist (vectorDyadicTailGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) j sample.1
      (vectorMeasureState μ β t ht r sample))
    (vectorMeasureGradient μ β t (projIcc (0 : ℝ) 1 zero_le_one r) sample.1
      (vectorMeasureState μ β t ht r sample))≤_
  exact vectorDyadicTailGradient_limit_dist_le μ β t ht _ j _ _

theorem integral_vectorFiniteControlGap_feedback_abs_le (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) (j : ℕ) :
    |∫sample,vectorFiniteControlGap (Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)) β t μ
      (vectorMeasureFeedbackControl μ β t ht.le) sample ∂vectorDisorderBrownianMeasure n|≤
      ((1-t)*β^2)/2*((vectorDyadicGradientError n β t j)^2+
        (n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j))) := by
  let s := Paper.parisiGridRSBScheme μ (vectorDyadicIndex j)
  let A := vectorMeasureFeedbackControl (n := n) μ β t ht.le
  let ε := vectorDyadicGradientError n β t j
  let c := (1-t)*β^2
  have hA := isVectorParisiControl_vectorMeasureFeedbackControl (n := n) μ β t ht.le
  have hε := vectorDyadicGradientError_nonneg n β t ht.le j
  have hc : 0≤c/2 := by dsimp only [c];positivity
  let w : ℝ≥0→VectorDisorderBrownianSample n→ℝ := fun r sample =>
    vectorFiniteControlSource s β t μ A r sample-vectorParisiControlCost c μ A r sample
  have hm : Measurable (Function.uncurry w) :=
    (measurable_vectorFiniteControlSource s β t μ A hA).sub (measurable_vectorParisiControlCost c μ A hA)
  have hbound (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) : ‖w r sample‖≤(7/2 : ℝ)*|c| *(n : ℝ) :=
    (norm_sub_le _ _).trans (by
      have h1 := norm_vectorFiniteControlSource_le s β t μ A hA r sample
      have h2 := norm_vectorParisiControlCost_le c μ A hA r sample
      change _≤(7/2 : ℝ)*|c| *(n : ℝ)
      dsimp only [c] at h2 ⊢
      linarith)
  have hi := integrable_vectorBoundedCellIntegral w hm 0 1 ((7/2 : ℝ)*|c| *(n : ℝ)).toNNReal
    (fun r sample=>by rw [Real.coe_toNNReal _ (by positivity)];exact hbound r sample)
  let g : ℝ≥0→ℝ := fun r=>c/2*(ε^2+(n : ℝ)*|Paper.parisiCDF μ r-Paper.parisiCDF (Paper.parisiSchemeMeasure s) r|)
  have hgi : IntegrableOn g (Ioc 0 1) nonnegativeLebesgueMeasure :=
    ((integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := ε^2)).add
      ((integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (n : ℝ))).const_mul (c/2)
  have hg : (∫r in Ioc 0 1,g r ∂nonnegativeLebesgueMeasure)=
      c/2*(ε^2+(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)) := by
    unfold g
    rw [integral_const_mul,integral_add
      (integrableOn_const (nonnegativeLebesgueMeasure_Ioc_ne_top 0 1) (C := ε^2))
      ((integrableOn_nnreal_CDF_abs_sub μ (Paper.parisiSchemeMeasure s)).const_mul (n : ℝ)),
      integral_const_mul,integral_nnreal_CDF_abs_sub]
    simp only [integral_const,Measure.real,Measure.restrict_apply_univ,nonnegativeLebesgueMeasure_Ioc,NNReal.coe_one,NNReal.coe_zero,
      sub_zero,ENNReal.ofReal_one,ENNReal.toReal_one,one_smul]
  have hs (sample : VectorDisorderBrownianSample n) :
      ‖∫r in Ioc 0 1,w r sample ∂nonnegativeLebesgueMeasure‖≤
        c/2*(ε^2+(n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiSchemeMeasure s)) := by
    have hh := norm_integral_le_of_norm_le hgi (show ∀ᵐr ∂nonnegativeLebesgueMeasure.restrict (Ioc 0 1),
        ‖w r sample‖≤g r from by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.norm_eq_abs]
      exact vectorFiniteControlSource_sub_cost_abs_le s β t ht.le μ A r sample ε hε
        (vectorFiniteControlGradient_feedback_sub_le μ β t ht.le j r hr.2 sample))
    rw [hg] at hh
    exact hh
  have hh := norm_integral_le_of_norm_le_const (μ := vectorDisorderBrownianMeasure n)
    (f := fun sample=>∫r in Ioc 0 1,w r sample ∂nonnegativeLebesgueMeasure)
    (Eventually.of_forall hs)
  rw [vectorFiniteControlGap_integral_eq s β t hβ ht μ A hA]
  simpa only [w,c,ε,s,Real.norm_eq_abs,probReal_univ,mul_one,FRSB.parisiSchemeMeasure_grid_eq] using hh

theorem integral_vectorMeasureControlGap_feedback_eq_zero (μ : Paper.ParisiMeasure) (β t : ℝ)
    (hβ : β≠0) (ht : t<1) :
    (∫sample,vectorMeasureControlGap μ β t (vectorMeasureFeedbackControl μ β t ht.le) sample
      ∂vectorDisorderBrownianMeasure n)=0 := by
  have hA := isVectorParisiControl_vectorMeasureFeedbackControl (n := n) μ β t ht.le
  have hL := (tendsto_integral_vectorFiniteControlGap_dyadic μ β t hβ ht _ hA).abs
  have hD := (Paper.tendsto_parisiCDFDistance_grid μ).comp tendsto_vectorDyadicIndex
  have hE := tendsto_vectorDyadicGradientError n β t
  have hR : Tendsto (fun j=>((1-t)*β^2)/2*((vectorDyadicGradientError n β t j)^2+
      (n : ℝ)*Paper.parisiCDFDistance μ (Paper.parisiGridMeasure μ (vectorDyadicIndex j)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_pow (by norm_num : (2 : ℕ)≠0),mul_zero,add_zero] using
      ((hE.pow 2).add (hD.const_mul (n : ℝ))).const_mul (((1-t)*β^2)/2)
  have hz := le_of_tendsto_of_tendsto hL hR
    (Eventually.of_forall (fun j=>integral_vectorFiniteControlGap_feedback_abs_le μ β t hβ ht j))
  exact abs_eq_zero.mp (le_antisymm hz (abs_nonneg _))

end QuantitativePaper
