module
public import QuantitativePaper.VectorDyadicWeightedVarianceLimit
public import QuantitativePaper.VectorMeasureConditionalVariance
public import FourPapersCommon.PastIntegralComparison

@[expose] public section

/-! The literal arbitrary-profile Hessian versus conditional-spin
variance inequality. The right CDF multiplies the lower bound even at
atoms, and the conditioning sees the entire enlarged Wiener past. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem integrable_vectorMeasureHessianQuadratic (μ : Paper.ParisiMeasure) (β t a : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    Integrable (vectorMeasureHessianQuadratic μ β t ht q w) (vectorMeasureDisorderTilt μ β t a) := by
  letI:=vectorMeasureDisorderTilt_probability (n:=n) μ β t a ht
  apply Integrable.of_bound
    ((adapted_vectorMeasureHessianQuadratic μ β t ht q w).mono
      ((vectorBrownianFiltration n).le _) le_rfl).aestronglyMeasurable ((n : ℝ)*‖w‖^2)
  exact .of_forall fun sample=>by
    simpa only [Real.norm_eq_abs] using vectorMeasureHessianQuadratic_bound μ β t ht q w sample

theorem vectorMeasureHessian_conditionalVariance_bounds (μ : Paper.ParisiMeasure)
    (β t a : ℝ) (hβ : β≠0) (ht : t<1) (q : Paper.Overlap) (w : Field n) :
    ∀ᵐsample ∂vectorMeasureDisorderTilt μ β t a,
      Paper.parisiCDF μ q*vectorMeasureConditionalVariance μ β t a ht.le q w sample≤
        vectorMeasureHessianQuadratic μ β t ht.le q w sample ∧
      vectorMeasureHessianQuadratic μ β t ht.le q w sample≤
        vectorMeasureConditionalVariance μ β t a ht.le q w sample := by
  let ambient : MeasurableSpace (VectorDisorderBrownianSample n):=inferInstance
  let P:=vectorMeasureDisorderTilt (n:=n) μ β t a
  let m:=vectorBrownianFiltration n (q : ℝ).toNNReal
  let C:=vectorMeasureConditionalVariance μ β t a ht.le q w
  let H:=vectorMeasureHessianQuadratic μ β t ht.le q w
  have hCm : StronglyMeasurable[m] C:=stronglyMeasurable_vectorMeasureConditionalVariance μ β t a ht.le q w
  have hHm : StronglyMeasurable[m] H:=(adapted_vectorMeasureHessianQuadratic μ β t ht.le q w).stronglyMeasurable
  have hCi : Integrable C P:=integrable_vectorMeasureConditionalVariance μ β t a ht.le q w
  have hHi : Integrable H P:=integrable_vectorMeasureHessianQuadratic μ β t a ht.le q w
  have htest (Z : VectorDisorderBrownianSample n→ℝ) (hZ : Measurable[m] Z)
      (hZn : ∀sample,0≤Z sample) (hZb : ∀sample,‖Z sample‖≤1) :
      (∫sample,Z sample*(Paper.parisiCDF μ q*C sample) ∂P)≤∫sample,Z sample*H sample ∂P ∧
      (∫sample,Z sample*H sample ∂P)≤∫sample,Z sample*C sample ∂P := by
    have hCb : ∀sample,‖Z sample‖≤(1 : ℝ≥0):=by simpa only [NNReal.coe_one] using hZb
    have he:=vectorMeasure_weighted_hessian_variance_bounds μ β t a hβ ht q w Z hZ 1 hCb hZn
    have hpair:=integral_vectorMeasureConditionalVariance_mul_past μ β t a ht.le q w Z hZ 1 hCb
    have hmul : (fun sample=>Z sample*(Paper.parisiCDF μ q*C sample))=
        fun sample=>Paper.parisiCDF μ q*(Z sample*C sample) := by funext sample;ring
    constructor
    · rw [hmul,integral_const_mul,hpair]
      exact he.1
    · rw [hpair]
      exact he.2
  have hleft : (fun sample=>Paper.parisiCDF μ q*C sample)≤ᵐ[P]H := by
    apply ae_le_of_past_bounded_nonneg_tests (m0:=ambient) m P ((vectorBrownianFiltration n).le _)
      _ H (hCm.const_mul _) hHm (hCi.const_mul _) hHi
    exact fun Z hZ hZn hZb=>(htest Z hZ hZn hZb).1
  have hright : H≤ᵐ[P]C := by
    apply ae_le_of_past_bounded_nonneg_tests (m0:=ambient) m P ((vectorBrownianFiltration n).le _)
      H C hHm hCm hHi hCi
    exact fun Z hZ hZn hZb=>(htest Z hZ hZn hZb).2
  exact hleft.and hright

end QuantitativePaper
