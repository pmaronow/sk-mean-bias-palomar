module
public import QuantitativePaper.VectorDyadicHessianPassage
public import QuantitativePaper.VectorMeasureGradientAdaptation

@[expose] public section

/-! Actual arbitrary-profile Hessian quadratic forms are adapted and
bounded. Positivity passes from the genuine finite Hessians. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter FourPapersCommon
open scoped NNReal Topology
namespace QuantitativePaper
open SpinGlass SpinGlass.Targets
set_option maxHeartbeats 1400000
set_option maxSynthPendingDepth 128
set_option synthInstance.maxHeartbeats 200000
variable {n : ℕ}

theorem continuous_vectorMeasureHessian_quadratic (μ : Paper.ParisiMeasure)
    (β t : ℝ) (ht : t≤1) (w : Field n) :
    Continuous (fun z : Paper.Overlap×VectorParameter n=>
      inner ℝ w (vectorMeasureHessian μ β t z.1 z.2.1 z.2.2 w)) :=
  continuous_const.inner ((continuous_vectorMeasureHessian μ β t ht).clm_apply continuous_const)

theorem adapted_vectorMeasureHessianQuadratic (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) :
    Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (vectorMeasureHessianQuadratic μ β t ht q w) := by
  have hq : Measurable[vectorBrownianFiltration n (q : ℝ).toNNReal]
      (fun _ : VectorDisorderBrownianSample n=>q) := measurable_const
  have hm := (continuous_vectorMeasureHessian_quadratic μ β t ht w).measurable.comp
    (hq.prodMk (adapted_vectorMeasureJointState μ β t ht (q : ℝ).toNNReal))
  dsimp only [Function.comp_def,vectorMeasureJointState] at hm
  exact hm

theorem vectorMeasureHessianQuadratic_bound (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    |vectorMeasureHessianQuadratic μ β t ht q w sample|≤(n : ℝ)*‖w‖^2 := by
  exact le_of_tendsto ((tendsto_vectorDyadicHessianQuadratic μ β t ht q w sample).abs)
    (.of_forall fun j=>vectorDyadicHessianQuadratic_bound μ β t ht q j w sample)

theorem vectorDyadicHessianQuadratic_nonneg (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (j : ℕ) (w : Field n)
    (sample : VectorDisorderBrownianSample n) :
    0≤vectorDyadicHessianQuadratic μ β t ht q j w sample :=
  vectorFieldHessian_quadratic_nonneg _ β t _ _ _ w

theorem vectorMeasureHessianQuadratic_nonneg (μ : Paper.ParisiMeasure) (β t : ℝ)
    (ht : t≤1) (q : Paper.Overlap) (w : Field n) (sample : VectorDisorderBrownianSample n) :
    0≤vectorMeasureHessianQuadratic μ β t ht q w sample :=
  ge_of_tendsto (tendsto_vectorDyadicHessianQuadratic μ β t ht q w sample)
    (.of_forall fun j=>vectorDyadicHessianQuadratic_nonneg μ β t ht q j w sample)

end QuantitativePaper
