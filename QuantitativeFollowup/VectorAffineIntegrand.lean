module
public import QuantitativeFollowup.VectorAffineDerivativeIntegral

@[expose] public section

/-! Joint measurability, uniform integrability and exact Fubini for the
literal time integrand of the actual affine-control derivative. -/
noncomputable section
open Set MeasureTheory QuantitativePaper StochasticCalculus FourPapersCommon
open scoped NNReal Topology
namespace QuantitativeFollowup
set_option maxHeartbeats 1000000
set_option maxSynthPendingDepth 128
variable {n : ℕ}

def vectorAffineDerivativeIntegrand (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (r : ℝ≥0)
    (sample : VectorDisorderBrownianSample n) : ℝ :=
  ((1-t)*β^2)*(Paper.parisiCDF ν r-Paper.parisiCDF μ r)*
    (inner ℝ (vectorTerminalGradient n β t sample.1
      (vectorControlledState ((1-t)*β^2) μ A 1 sample)) (A r sample)-‖A r sample‖^2/2)

theorem measurable_vectorAffineDerivativeIntegrand (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    Measurable (Function.uncurry (vectorAffineDerivativeIntegrand μ ν β t A)) := by
  have hX := (measurable_vectorControlledState ((1-t)*β^2) μ A hA).of_uncurry_left (x:=1)
  have hv := (continuous_vectorTerminalGradient (n:=n) β t).measurable.comp
    (measurable_fst.prodMk hX)
  have hcoef : Measurable (fun z : ℝ≥0×VectorDisorderBrownianSample n=>
      ((1-t)*β^2)*(Paper.parisiCDF ν z.1-Paper.parisiCDF μ z.1)) :=
    measurable_const.mul (((Paper.parisiCDF_monotone ν).measurable.sub
      (Paper.parisiCDF_monotone μ).measurable).comp
        (NNReal.continuous_coe.measurable.comp measurable_fst))
  exact hcoef.mul (((hv.comp measurable_snd).inner hA.measurable).sub
    ((hA.measurable.norm.pow_const 2).div_const 2))

theorem norm_vectorAffineDerivativeIntegrand_le (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A)
    (r : ℝ≥0) (sample : VectorDisorderBrownianSample n) :
    ‖vectorAffineDerivativeIntegrand μ ν β t A r sample‖≤3*|(1-t)*β^2| *(n:ℝ) := by
  let c:=(1-t)*β^2
  let v:=vectorTerminalGradient n β t sample.1 (vectorControlledState c μ A 1 sample)
  have hA2 : ‖A r sample‖^2≤(n:ℝ):=by
    nlinarith [hA.norm_le r sample,Real.sq_sqrt (Nat.cast_nonneg n),norm_nonneg (A r sample)]
  have hv : ‖v‖≤Real.sqrt (n:ℝ):=norm_vectorTerminalGradient_le β t sample.1 _
  have hi : ‖inner ℝ v (A r sample)‖≤(n:ℝ):=by
    calc
      _≤‖v‖*‖A r sample‖:=norm_inner_le_norm _ _
      _≤Real.sqrt (n:ℝ)*Real.sqrt (n:ℝ):=
        mul_le_mul hv (hA.norm_le r sample) (norm_nonneg _) (Real.sqrt_nonneg _)
      _=(n:ℝ):=Real.mul_self_sqrt (Nat.cast_nonneg n)
  have ht : ‖inner ℝ v (A r sample)-‖A r sample‖^2/2‖≤3*(n:ℝ)/2 := by
    have hh:=norm_sub_le (inner ℝ v (A r sample)) (‖A r sample‖^2/2)
    rw [Real.norm_of_nonneg (div_nonneg (sq_nonneg ‖A r sample‖) (by norm_num : (0:ℝ)≤2))] at hh
    linarith
  have hc : ‖c*(Paper.parisiCDF ν r-Paper.parisiCDF μ r)‖≤|c|:=by
    rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
    have hh : |Paper.parisiCDF ν r-Paper.parisiCDF μ r|≤1:=
      abs_le.mpr ⟨by linarith [Paper.parisiCDF_nonneg ν r,Paper.parisiCDF_le_one μ r],
        by linarith [Paper.parisiCDF_le_one ν r,Paper.parisiCDF_nonneg μ r]⟩
    exact (mul_le_mul_of_nonneg_left hh (abs_nonneg c)).trans_eq (mul_one _)
  change ‖(c*(Paper.parisiCDF ν r-Paper.parisiCDF μ r))*
    (inner ℝ v (A r sample)-‖A r sample‖^2/2)‖≤3*|c| *(n:ℝ)
  rw [norm_mul]
  calc
    _≤|c| *(3*(n:ℝ)/2):=mul_le_mul hc ht (norm_nonneg _) (abs_nonneg c)
    _≤3*|c| *(n:ℝ):=by nlinarith [mul_nonneg (abs_nonneg c) (Nat.cast_nonneg n)]

theorem integral_vectorAffineControlDerivative_eq_time_integral
    (P : Measure (VectorDisorderBrownianSample n)) [IsProbabilityMeasure P]
    (μ ν : Paper.ParisiMeasure) (β t : ℝ)
    (A : ℝ≥0→VectorDisorderBrownianSample n→Field n) (hA : IsVectorParisiControl A) :
    (∫sample,vectorAffineControlDerivative μ ν β t A 0 sample∂P)=
      ∫r in Ioc 0 1,(∫sample,vectorAffineDerivativeIntegrand μ ν β t A r sample∂P)
        ∂nonnegativeLebesgueMeasure := by
  have he:=bounded_nnreal_time_fubini P (vectorAffineDerivativeIntegrand μ ν β t A)
    (measurable_vectorAffineDerivativeIntegrand μ ν β t A hA) 1 (3*|(1-t)*β^2| *(n:ℝ)).toNNReal
    (fun r _ sample=>by
      rw [Real.coe_toNNReal _ (by positivity)]
      exact norm_vectorAffineDerivativeIntegrand_le μ ν β t A hA r sample)
  rw [←he.2]
  apply integral_congr_ae
  exact .of_forall (vectorAffineControlDerivative_eq_time_integral μ ν β t A hA)

end QuantitativeFollowup
